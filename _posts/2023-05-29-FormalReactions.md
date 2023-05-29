\section*{Assignment on First Integrals}

\subsection*{1}
Suppose \(H \in C^1( \Omega)\). 
Prove that it is the first integral of the differential  equation 
\begin{equation}
\dot{x}=f \circ x \label{eq:ODE}
\end{equation} 
if and only 
if \(H'(\xi)f(\xi)=0\) for all points \(\xi \in \Omega\)
\subsubsection*{Solution}
A) Suppose  \(H \in C^1\) is a first integral of $\dot{x}=f \circ x $. Then, \(H\)must satisfy the following equation:
\[H(x(t))=\mathrm{const.}\]
for all solutions of Eq.\eqref{eq:ODE}. 
This implies that
\[\ddt{H(x(t))}=0,\] or
\[\ddt{H(x(t))}=H'(x(t))\cdot \dot{x}(t)=H'(x(t))\cdot f(x(t))\]
for all \(t\) in the domain of the solution of Eq.\eqref{eq:ODE}.
Let us take a solution starting from the point \(\xi: x(0)=\xi.\)
\[0=H'(x(0))\cdot  f(x(0))=
H'(\xi)\cdot  f(\xi).\]\textbf{
B) Conversely, assume that
\[H'(\xi)f(\xi)=0\] for all \(\xi\in \Omega,\)
and let us calculate the ("time") derivative of \(H\) along the solutions.
\[\ddt{H(x(t))}=H'(x(t))\cdot \dot{x}(t)=H'(x(t))\cdot f(x(t))=0.\]
The fact that this is zero shows, that \(H\) is a first integral.}

\textbf{This below is what you had earlier. I do not delete it, maybe you can defend that it is useful.}
Now, let \(\xi\) be any point in \(\Omega\). Then, we have:
 \(H'(\xi)f(\xi)=0\) for all \(\xi \in \Omega\)



\noindent
Suppose \(H'(\xi)f(\xi)=0\) for all \(\xi \in \Omega\), then we can define a function \(H(x)\) as follows;
\[H(x) = \int_0^x H'(t) dt\]
This function is continuous and differentiable, and it satisfies the following equation:
\(H'(x) = f(x)\) for all points \(x \in \Omega\)
Therefore, \(H \in C^1\)is a first integral of \(\dot{x}=f \circ x \).
In conclusion \(H \in C^1\) is a first integral of differential  equation \(\dot{x}=f \circ x \) if and only if \(H'(\xi)f(\xi)=0\)for all points \(\xi \in \Omega\).

\subsection*{2} 
A)
To find two independent linear first integrals for the Michaelis--Menten reaction.
\subsubsection*{Solution}
The Michaelis-Menten reaction induces the following differential equation:
\begin{align*}
\dot{E} &= (k_{-1}+k_2)C - k_1 ES\\
\dot{S} &= k_{-1} C - k_1 ES\\
\dot{C} &=-(k_{-1}+k_2) C + k_1 ES \\
\dot{P} &= k_2 C
\end{align*}
We are looking for a linear function \(H\)  such that the following equation holds:
\begin{equation*}
\ddt{H}=\frac{\partial H}{\partial E} \dot{E} + \frac{\partial H}{\partial S} \dot{S} +\frac{\partial H}{\partial C} \dot{C} + \frac{\partial H}{\partial P} \dot{P} =0
%    \frac{dH}{dt}=\frac{\partial H}{\partial E} \dot{E} + \frac{\partial H}{\partial S} \dot{S} %+\frac{\partial H}{\partial C} \dot{C} + \frac{\partial H}{\partial P} \dot{P} =0
\end{equation*}
The function \(H(E,S,C,P):=E+C\) satisfies this condition, since 
\(
    \frac{\partial H}{\partial E}=1, \quad
    \frac{\partial H}{\partial S}=0, \quad
    \frac{\partial H}{\partial C}=1, \quad
    \frac{\partial H}{\partial P}=0
    \)
    Thus we have, \[1((k_{-1}+k_2)C - k_1 ES) + 1(-(k_{-1}+k_2) C + k_1 ES ) = 0\]

    \noindent
    Similarly, the function \(H_2(E,S,C, P)=S+C+P\) is the first integral of this system.

Independence of the obtained first integrals means that the vectors 
\(\begin{bmatrix}1\\0\\1\\0\end{bmatrix}\) and 
\(\begin{bmatrix}0\\1\\1\\1\end{bmatrix}\)---defining the two first integrals---are linearly independent. If the first integral is non-linear, as in the case of the Lotka--Volterra equations, then the definition is more complicated. 

B)
The general form of kinetic differential equations, given that the kinetic is of the mass-action type, is:
\(\dot{\cb}=\gammab\cdot\diag(\kb)\circ(\cb)^{\alphab}.\)
Write the MM-eq. in this form. (Pages 79--81.)
\textbf{ This is missing, but let us leave it now.}

In the case of the Michaelis--Menten reaction, we have :
\[
\gammab = \begin{bmatrix}
    -1 & 1 & 1 \\
    -1 & 1 & 0 \\
    1 & -1 & -1 \\
    0 & 0 & 1 \\
\end{bmatrix},
\quad
\alphab = \begin{bmatrix}
    1 & 0 & 0 \\
    1 & 0 & 0 \\
    0 & 1 & 1 \\
    0 & 0 & 0 \\
\end{bmatrix}
\]
We can write the induced kinetic differential equation in the form:
\begin{equation}\label{eq:gende}
    \dot{\cb} = ( \gammab \cdot\diag(\kb))\cdot \cb^{\alphab},
\end{equation}
This form shows that the vectors in the left kernel of \(\alphab\) can play the role of linear first integrals.
\textbf{END of the solution of the problem follows} as
\begin{align}\label{eq:genMM}
    \dot{\cb} &= \begin{bmatrix}
    -1 & 1 & 1 \\
    -1 & 1 & 0 \\
    1 & -1 & -1 \\
    0 & 0 & 1 \\
\end{bmatrix} \cdot\diag(k_1,k_{-1},k_2)\cdot \cb^{\begin{bmatrix}
    1 & 0 & 0 \\
    1 & 0 & 0 \\
    0 & 1 & 1 \\
    0 & 0 & 0 \\
\end{bmatrix}}\\
&=
\begin{bmatrix}
    -1 & 1 & 1 \\
    -1 & 1 & 0 \\
    1 & -1 & -1 \\
    0 & 0 & 1 \\
\end{bmatrix} \cdot\begin{bmatrix}k_1E^1S^1C^0P^0\\ k_{-1}E^0S^0C^1P^0\\ k_2E^0S^0C^1P^0\end{bmatrix}=
\left[\begin{array}{l}
\dot{E}=(k_{-1}+k_2)C - k_1 ES\\
\dot{S}=k_{-1} C - k_1 ES\\
\dot{C}=-(k_{-1}+k_2) C + k_1 ES\\
\dot{P}= k_2 C
\end{array}\right].
\end{align}
\textbf{\textit{Well understood}}
The left kernel of the matrix \(\gammab\) are vectors \(\xb\) such that \(\xb^T \gammab = 0\). The vector \(\xb_1 = \begin{bmatrix} 1\\0\\1\\0\end{bmatrix}\) is a basis of left kernel of \(\gammab\).
Another basis of the left kernel of \(\gammab\) is the vector \(\xb_2 = \begin{bmatrix}0\\1\\1\\1\\ \end{bmatrix}\)

\textbf{Do the same for \ce{A + B <=> C.}}


In this case, we have the following:
\[\gammab = \begin{bmatrix}
    -1 & 1\\ -1 & 1\\ 1 & -1 \\
\end{bmatrix}
\quad,
\alphab = \begin{bmatrix}
    1 & 0\\ 1 & 0\\ 0 & 1 \\
\end{bmatrix}
\]
Writing in the form of \eqref{eq:gende} we have
\begin{align}
\dot{c} &= \begin{bmatrix}-1 & 1\\ -1 & 1\\ 1 & -1 \\ \end{bmatrix}\cdot \diag (k_1,k_{-1}) \cdot \cb^{\begin{bmatrix}1 & 0\\ 1 & 0\\ 0 & 1 \\ \end{bmatrix}}\\
&=  \begin{bmatrix}-1 & 1\\ -1 & 1\\ 1 & -1 \\ \end{bmatrix}\cdot
\begin{bmatrix}k_1a^1b^1c^0\\ k_{-1}a^0b^0c^1\\ \end{bmatrix} = \begin{bmatrix}
    -k_1ab+k_{-1}c\\ -k_1ab+k_{-1}c\\k_1ab-k_{-1}c
\end{bmatrix} = \begin{bmatrix}
    \dot{a} = -k_1ab+k_{-1}c\\ \dot{b} =-k_1ab+k_{-1}c\\ \dot{c}= k_1ab-k_{-1}c\\
\end{bmatrix}
\end{align}
Here, the non-trivial vectors \(\xb_1 = \begin{bmatrix} 1\\-1\\0\\ \end{bmatrix}\) and \(\xb_2 = \begin{bmatrix}-1\\1\\0\\ \end{bmatrix}\) forms basis for the left kernel of \(\gammab\)

From the left kernels \(\xb_1\) and \(\xb_2\) above  we can observe that the the function \(H(a,b,c)=a-b\) and \(H(a,b,c)=-a+b\) are first integrals of the system \(\dot{c}\).
\subsection*{3}
To verify that \(H(x,y)= x + y - \log[x] - \log[y]\) is the first integral of the following Lotka-Volterra equation:
\begin{align*}
    \dot{x} &= x-xy\\
    \dot{y} &= xy - y
\end{align*}

\subsubsection*{Solution}
    \(H(x,y)\) is the first integral of the above differential equation if the following equation holds:
    \[\ddt{H}=\frac{\partial H}{\partial x} \dot{x} + \frac{\partial H}{\partial y} \dot{y} =0 \]
In this case, we have the following: 
\begin{align*}
    \frac{\partial H}{\partial x} &= \Bigg(1-\frac{1}{x}\Bigg) \\
    \frac{\partial H}{\partial y} &= \Bigg(1-\frac{1}{y}\Bigg)
\end{align*}
Thus: \[ \ddt{H} = \Bigg(1-\frac{1}{x}\Bigg)(x-xy)+\Bigg(1-\frac{1}{y}\Bigg)(xy - y)=0\]

\noindent
Therefore, the given function \(H\) is the   first integral of the specialized Lotka--Volterra system above.
\subsection*{4: A method to find a first integral}
Consider the Lotka--Volterra equation in the open first quadrant:
\(\dot{x}(t) = x(t)-x(t)y(t),\quad
    \dot{y}(t) = x(t)y(t) - y(t).\)
As the values of the functions are strictly positive, one may divide 
through the two sides.
\[
\frac{\dot{x}(t)}{x(t)}=1-y(t),\quad
\frac{\dot{y}(t)}{y(t)}=x(t)-1.\]
Let us multiply the two equations, taking the sides in the appropriate order.
\[\frac{\dot{x}(t)}{x(t)}(x(t)-1)=(1-y(t))\frac{\dot{y}(t)}{y(t)}.
\]
Expand the products. 
\[\dot{x}(t)-
\frac{\dot{x}(t)}{x(t)}=\frac{\dot{y}(t)}{y(t)}-\dot{y}(t).
\]
Let us integrate both sides to get:
\[x(t)-\log(x(t))=\log(y(t))-y(t)+const.\]
