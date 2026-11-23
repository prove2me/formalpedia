-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_theorem_9
-- name    : LogBarrierIPM.Iterations.Supplement.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:14:45.102631+00:00
-- url     : https://prove2.me/theorems/95b10c3d-b091-4cf4-a844-e6ba91c8070a
-- title:
--   Theorem 9 — directed logarithmic Hausdorff convergence
-- statement:
--   For every Puiseux polyhedron $\mathcal P=\{x\in K^d:Ax\le b\}\subseteq K_+^d$, $d\ge1$,
--   $$d_H(\log_t\mathcal P(t),\operatorname{val}(\mathcal P))\longrightarrow0\qquad(t\longrightarrow+\infty).$$
--   The direction is from $\log_t\mathcal P(t)$ to $\operatorname{val}(\mathcal P)$. The statement also records the eventually nonnegative real specializations that make this logarithm meaningful. No reverse-distance assertion is included. This is the qualitative approximation underlying the neighborhood estimates.
--
--   Differences from the source:
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: directed distance converges to zero → nonnegative extended-real directed distance, with empty-source value 0 and empty-target value +∞; reason: this includes empty polyhedra; the positive-epsilon criterion is exactly convergence to zero
--   - reading: log_t P(t) is formed for large t → an additional clause that P(t) lies in the nonnegative orthant for all large t; reason: the logarithm is defined there only; the proof on p. 11 states that the evaluated generators are nonnegative
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 11, Theorem 9

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem theorem_9 {p d : ℕ} (hd : 1 ≤ d)
    (A : Matrix (Fin p) (Fin d) Puiseux) (b : Fin p → Puiseux)
    (horthant : kOrthant (kPolyhedron A b)) :
    (∀ᶠ t in atTop, ∀ x ∈ realPolyhedron A b t, ∀ i, 0 ≤ x i) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t in atTop,
      hausdorffH (logImage t (realPolyhedron A b t))
        (valVec '' kPolyhedron A b) ≤ (ε : EReal) := by sorry

end LogBarrierIPM.Iterations.Supplement
