-- Prove2me | Theorems.Thm_Matrix_trace_symmetricPower_fin_two
-- name    : Matrix.trace_symmetricPower_fin_two
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T13:37:18.431162+00:00
-- url     : https://prove2.me/theorems/6417ff5c-64d9-5649-a096-d1ae0378b3b1
-- title:
--   Trace of the $n$-th symmetric power of a $2\times 2$ matrix: $\operatorname{tr}\operatorname{Sym}^n A = U_n(\operatorname{tr}A, \det A)$ (Chebyshev polynomials of the second kind)
-- statement:
--   Let $R$ be a commutative ring, $n \ge 0$, and $A = \begin{pmatrix} a_{00} & a_{01} \\ a_{10} & a_{11} \end{pmatrix}$ a $2 \times 2$ matrix over $R$, with trace $t = a_{00} + a_{11}$ and determinant $d = a_{00}a_{11} - a_{01}a_{10}$. The matrix $A$ acts on $R^2 = Rx \oplus Ry$ by $x \mapsto a_{00}x + a_{10}y$, $y \mapsto a_{01}x + a_{11}y$, and hence on the space $\operatorname{Sym}^n(R^2)$ of homogeneous polynomials of degree $n$ in $x, y$. Let $S = \operatorname{Sym}^n A$ be the $(n+1) \times (n+1)$ matrix of this action in the basis $x^i y^{n-i}$ ($0 \le i \le n$): its entry $S_{ij}$ is the coefficient of $x^i y^{n-i}$ in $(a_{00}x + a_{10}y)^j (a_{01}x + a_{11}y)^{n-j}$, that is, the coefficient of $X^i$ in $(a_{00}X + a_{10})^j (a_{01}X + a_{11})^{n-j} \in R[X]$. Define $U_k = U_k(t, d) \in R$ by
--
--   $$U_0 = 1, \qquad U_1 = t, \qquad U_{k+2} = t\,U_{k+1} - d\,U_k .$$
--
--   Then:
--
--   1. $\operatorname{tr} \operatorname{Sym}^n A = U_n(\operatorname{tr} A, \det A)$.
--   2. If $\det A = 1$ and $\operatorname{tr} A = 2x$ for some $x \in R$, then $\operatorname{tr} \operatorname{Sym}^n A = U_n(x)$, the value at $x$ of the Chebyshev polynomial of the second kind ($U_n(\cos\theta) = \sin((n+1)\theta)/\sin\theta$).
--   3. If $\operatorname{tr} A = \alpha + \beta$ and $\det A = \alpha\beta$ for some $\alpha, \beta \in R$ (i.e. the characteristic polynomial of $A$ is $(X - \alpha)(X - \beta)$), then for every $m \ge 0$
--
--   $$\operatorname{tr}\big((\operatorname{Sym}^n A)^m\big) = \sum_{i=0}^{n} \alpha^{mi} \beta^{m(n-i)} .$$
--
--   So $\operatorname{Sym}^n A$ behaves as if it had the eigenvalues $\alpha^i \beta^{n-i}$, over any commutative ring. For $m = 1$ the right side is the complete homogeneous symmetric polynomial $h_n(\alpha, \beta)$, equal to $(\alpha^{n+1} - \beta^{n+1})/(\alpha - \beta)$ when $\alpha - \beta$ is invertible. For example, for $n = 2$ and $A = \begin{pmatrix} a & b \\ c & e \end{pmatrix}$, $\operatorname{tr}\operatorname{Sym}^2 A = a^2 + ae + e^2 + bc = t^2 - d$.
--
--   Role: part 2 is the Weyl character formula for $\mathrm{SU}(2)$ (the character of the $(n+1)$-dimensional irreducible representation at $\operatorname{diag}(e^{i\theta}, e^{-i\theta})$ is $\sin((n+1)\theta)/\sin\theta$). Part 3 is the Frobenius-trace input of symmetric power $L$-functions: if $\alpha_p, \beta_p$ are the Satake parameters of a Hecke eigenform or of an elliptic curve at $p$, the local factor of $L(\operatorname{Sym}^n, s)$ has trace of $m$-th powers $\sum_i \alpha_p^{mi} \beta_p^{m(n-i)}$, the identity used in the symmetric power approach to the Ramanujan-Petersson and Sato-Tate bounds.
--
--   **Formalization Note**: Indices are `0, 1` (`Fin 2`) and `0, ..., n` (`Fin (n + 1)`); `A i j` is the entry in row `i`, column `j`, and `S i j` likewise, so `S` acts on coordinate columns in the basis $x^0 y^n, x^1 y^{n-1}, \dots, x^n y^0$. The matrix $S$ is a variable `S` with the defining hypothesis `hS`, which gives each entry as `Polynomial.coeff` of the dehomogenized product in `R[X]` (`Polynomial.C r` is the constant $r$ and `n - (j : ℕ)` is ordinary subtraction since $j \le n$). The sequence $U_k(t, d)$ is a function `u : ℕ → R` with the three defining hypotheses `hu0`, `hu1`, `hu` for $t = $ `A.trace` and $d = $ `A.det`; these determine `u` uniquely. `Polynomial.Chebyshev.U R (n : ℤ)` is Mathlib's Chebyshev polynomial of the second kind ($U_0 = 1$, $U_1 = 2X$, $U_{k+2} = 2X U_{k+1} - U_k$) and `.eval x` its value at $x$; the hypothesis `A.trace = 2 * x` is used instead of $x = t/2$ so that $2$ need not be invertible in $R$. `(S ^ m).trace` is the trace of the $m$-th matrix power. The three conjuncts are parts 1, 2 and 3.
-- source:
--   W. Fulton and J. Harris, Representation Theory: A First Course, GTM 129, Springer 1991, Lecture 11 (representations of sl_2 and SU(2), symmetric powers), doi:10.1007/978-1-4612-0979-9

import Mathlib

set_option autoImplicit false

theorem Matrix.trace_symmetricPower_fin_two {R : Type} [CommRing R] (n : ℕ)
    (A : Matrix (Fin 2) (Fin 2) R) (S : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hS : ∀ i j : Fin (n + 1), S i j =
      ((Polynomial.C (A 0 0) * Polynomial.X + Polynomial.C (A 1 0)) ^ (j : ℕ) *
        (Polynomial.C (A 0 1) * Polynomial.X + Polynomial.C (A 1 1)) ^ (n - (j : ℕ))).coeff (i : ℕ))
    (u : ℕ → R) (hu0 : u 0 = 1) (hu1 : u 1 = A.trace)
    (hu : ∀ k : ℕ, u (k + 2) = A.trace * u (k + 1) - A.det * u k) :
    S.trace = u n ∧
    (∀ x : R, A.trace = 2 * x → A.det = 1 → S.trace = (Polynomial.Chebyshev.U R (n : ℤ)).eval x) ∧
    (∀ α β : R, A.trace = α + β → A.det = α * β → ∀ m : ℕ,
      (S ^ m).trace = ∑ i ∈ Finset.range (n + 1), α ^ (m * i) * β ^ (m * (n - i))) := by
  sorry
