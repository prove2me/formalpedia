-- Prove2me | Theorems.Thm_MifflinSemismooth_Composition_eq_4_2
-- name    : MifflinSemismooth.Composition.eq_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:48:21.672376+00:00
-- url     : https://prove2.me/theorems/06789a9d-596b-405f-8def-4bd12add0746
-- title:
--   Equation (4.2) — gradient of a differentiable composite belongs to G
-- statement:
--   For the locally Lipschitz functions of Theorem 4, if the composite $F=E\circ Y$ is differentiable at $x$, then its ordinary gradient belongs to the chain-rule set:
--
--   $$\nabla F(x)\in G(x). $$
--
--   This is the differentiability-point claim used in the proof of the generalized-gradient chain rule.
-- source:
--   Mifflin, Semismooth and semiconvex functions in constrained optimization, IIASA Research Report RR-76-21 (December 1976), p. 12, proof of Theorem 4, display (4.2)

import Mathlib
import Definitions.Def_MifflinSemismooth_Composition_Setting
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded

namespace MifflinSemismooth.Composition

theorem eq_4_2 {n m : ℕ}
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (E : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ∀ i, ClarkeGradients.Shared.LipschitzOnBounded (f i))
    (hE : ClarkeGradients.Shared.LipschitzOnBounded E)
    (x : EuclideanSpace ℝ (Fin n))
    (hDiff : DifferentiableAt ℝ (compF E f) x) :
    gradient (compF E f) x ∈ G E f x := by sorry

end MifflinSemismooth.Composition
