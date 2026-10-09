-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_P8_norm
-- name    : IQCAlg.HeavyBall.P8_norm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:20:51.636994+00:00
-- url     : https://prove2.me/theorems/e0fecb34-b595-4d8d-9b35-8a66096a1a6b
-- title:
--   Appendix B, p. 40 — ‖P⁸‖² < 1/2 in the induced 2-norm
-- statement:
--   Let $P=\begin{bmatrix}-4/3&-4/9\\1&0\end{bmatrix}$ and let $\|\cdot\|$ be the operator norm induced by the Euclidean norm on $\mathbb R^2$. Then
--   $$\|P^8\|^2<\tfrac12 .$$
--   (Numerically $\|P^8\|^2\approx0.46044$.)
--
--   Consequently $P^8$ is a contraction, which turns the linear perturbation recursion into a monotone decrease of the error every eight steps.
--
--   **Formalization Note** The norm is Mathlib's $\ell^2$ operator norm on matrices, activated by `open scoped Matrix.Norms.L2Operator`; without it, `Matrix` carries no norm (and the entrywise sup norm, which is not the page's norm, is the other common choice).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 40, ‖P⁸‖² ≈ 0.46044 < 1/2

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting
open scoped Matrix.Norms.L2Operator

namespace IQCAlg.HeavyBall

/-- p. 40: `‖P⁸‖² < 1/2` for the induced 2-norm (Mathlib's `ℓ²` operator norm on matrices). -/
theorem P8_norm : ‖Pm ^ 8‖ ^ 2 < 1 / 2 := by sorry

end IQCAlg.HeavyBall
