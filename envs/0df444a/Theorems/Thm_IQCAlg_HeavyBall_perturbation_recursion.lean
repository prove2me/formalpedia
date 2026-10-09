-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_perturbation_recursion
-- name    : IQCAlg.HeavyBall.perturbation_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:56.349656+00:00
-- url     : https://prove2.me/theorems/84af80af-f95e-499e-afca-2d96b55d1294
-- title:
--   Appendix B, p. 40 — on the cycle's pieces, (ε_{k+2}, ε_{k+1}) = P (ε_{k+1}, ε_k)
-- statement:
--   Let $(x_k)_{k\ge0}$ be a real sequence satisfying (B.1) for every $k$, let $x^\star_k$ be the 3-cycle $p,q,r,p,\dots$ of (B.3), and let $\varepsilon_k=x_k-x^\star_k$. Fix $k$ and assume that $x_{k+1}$ lies on the same linear piece of (4.11) as $x^\star_{k+1}$: if $x^\star_{k+1}<1$ then $x_{k+1}<1$, and if $x^\star_{k+1}>2$ then $x_{k+1}>2$. Then
--   $$\begin{bmatrix}\varepsilon_{k+2}\\ \varepsilon_{k+1}\end{bmatrix}=P\begin{bmatrix}\varepsilon_{k+1}\\ \varepsilon_{k}\end{bmatrix},\qquad P=\begin{bmatrix}-4/3&-4/9\\1&0\end{bmatrix}.$$
--
--   Near the cycle the nonlinear recursion is therefore a linear time-invariant recursion for the perturbation, which is what the remaining steps of the argument analyse.
--
--   **Formalization Note** The same-piece condition is stated, as on the page, by membership of the iterate in the piece of its limit point; it is needed only at index $k+1$, the argument of $\nabla f$ in (B.1).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, perturbation recursion (the display defining P)

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- Perturbation recursion, p. 40: if `x` satisfies (B.1) and the iterate `x_{k+1}` lies on
the same piece of (4.11) as `x⋆_{k+1}`, then `(ε_{k+2}, ε_{k+1}) = P (ε_{k+1}, ε_k)`, i.e.
`ε_{k+2} = −(4/3) ε_{k+1} − (4/9) ε_k`. -/
theorem perturbation_recursion (x : ℕ → ℝ) (hx : IsB1Traj x) (k : ℕ)
    (hpiece : (cyc (k + 1) < 1 → x (k + 1) < 1) ∧ (2 < cyc (k + 1) → 2 < x (k + 1))) :
    ![eps x (k + 2), eps x (k + 1)] = Pm.mulVec ![eps x (k + 1), eps x k] := by sorry

end IQCAlg.HeavyBall
