-- Prove2me | Theorems.Thm_InverseGalois_regular_inverse_galois_alternating
-- name    : InverseGalois.regular_inverse_galois_alternating
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-13T17:29:00.582668+00:00
-- url     : https://prove2.me/theorems/f91903dd-25cb-4d44-b741-f4b126e9f940
-- title:
--   Alternating groups are realizable over $\mathbb{Q}(t)$
-- statement:
--   For every natural number $n$, the alternating group $A_n$ is the Galois group of a Galois extension of the rational function field $\mathbb{Q}(t)$. A realization of a group over $\mathbb{Q}(t)$ is called *regular*.
--
--   This is the **geometric half** of Hilbert's theorem that $A_n$ is realizable over $\mathbb{Q}$; combined with the specialization step supplied by Hilbert's irreducibility theorem (`InverseGalois.inverse_galois_problem_hilbert_descent`), it yields realizability of $A_n$ over $\mathbb{Q}$ itself.
--
--   Unlike the symmetric case, $A_n$ is not the Galois group of the generic polynomial of degree $n$, and the fundamental theorem of symmetric functions gives no purchase: the field of $A_n$-invariant rational functions in $n$ variables is $\mathbb{Q}(e_1,\dots,e_n)(\delta)$, where $e_1,\dots,e_n$ are the elementary symmetric polynomials and $\delta = \prod_{i<j}(x_i-x_j)$, and whether that field is purely transcendental over $\mathbb{Q}$ is **Noether's problem for $A_n$**, settled affirmatively only for $n \le 5$ and open for $n \ge 6$. Hilbert's construction therefore proceeds not through invariants of the natural permutation action but through an explicitly chosen one-parameter family.
--
--   **The construction of the source.** Normalize the trinomial family as
--   $$ g(y,t) \;=\; y^n - nty + (n-1)t . $$
--   Its Galois group over $\mathbb{Q}(t)$ is the full symmetric group $S_n$: the family is irreducible over $\mathbb{Q}(t)$, its group is doubly transitive, and specializing at $t = 1$ — where $g$ acquires a double root at $y = 1$ and $n-2$ simple roots — exhibits a transposition; a finite doubly transitive permutation group containing a transposition is the full symmetric group. The discriminant is
--   $$ \operatorname{disc}_y g(y,t) \;=\; (-1)^{\frac{n(n-1)}{2}}\, n^n (n-1)^{n-1}\, t^{n-1}(1-t), $$
--   which is not in general a square, consistent with the group being $S_n$ rather than $A_n$.
--
--   The subextension fixed by $A_n$ is the quadratic extension of $\mathbb{Q}(t)$ obtained by adjoining a square root of this discriminant, and the content of the construction is that **this quadratic extension is again a rational function field**. It is exhibited by a substitution depending on the parity of $n$.
--
--   *Odd degree.* Put $t = 1 - (-1)^{\frac{n(n-1)}{2}} n u^2$. The discriminant becomes
--   $$ n^{n+1}(n-1)^{n-1} t^{n-1} u^2, $$
--   a square when $n$ is odd, since then $n+1$, $n-1$ and $n-1$ are all even.
--
--   *Even degree.* Put $t = \bigl(1 + (-1)^{\frac{n(n-1)}{2}}(n-1)u^2\bigr)^{-1}$. The discriminant becomes
--   $$ n^n (n-1)^n t^n u^2, $$
--   a square when $n$ is even.
--
--   In either case $t$ is a rational function of $u$ of degree two, so $\mathbb{Q}(u)$ is a quadratic extension of $\mathbb{Q}(t)$; and in either case the square root of the discriminant equals $u$ times an element of $\mathbb{Q}(t)$, so that quadratic extension is exactly $\mathbb{Q}(t)(\sqrt{\operatorname{disc}}) = \mathbb{Q}(u)$. By the Galois correspondence the group of $g$ over $\mathbb{Q}(u)$ is the index-two subgroup of $S_n$ fixing $\sqrt{\operatorname{disc}}$, namely $A_n$. Hence $A_n$ is regularly realized over the rational function field $\mathbb{Q}(u)$, which is the assertion.
--
--   Small $n$ is included: for $n \le 2$ the group $A_n$ is trivial, and for $n = 3$ it is cyclic of order three.
-- source:
--   Inverse Galois problem, Wikipedia, https://en.wikipedia.org/wiki/Inverse_Galois_problem (revision of 13 September 2026), sections 'Symmetric and alternating groups' and 'Alternating groups' (the family g(y,t) = y^n - nty + (n-1)t, its discriminant (-1)^(n(n-1)/2) n^n (n-1)^(n-1) t^(n-1)(1-t), and the odd- and even-degree substitutions t = 1 - (-1)^(n(n-1)/2) n u^2 and t = 1/(1 + (-1)^(n(n-1)/2)(n-1)u^2)); Hilbert's irreducibility theorem and regular realizations as in Serre, Topics in Galois Theory, ch. 3; Noether's problem for A_n as in Maeda, 'Noether's problem for A_5', J. Algebra 125 (1989), 418-430

import Mathlib
import Definitions.Def_InverseGalois_realizability

namespace InverseGalois

theorem regular_inverse_galois_alternating (n : ℕ) :
    IsRealizable (RatFunc ℚ) (alternatingGroup (Fin n)) := by sorry

end InverseGalois
