-- Prove2me | Theorems.Thm_GlobalTheory_SimpleRoots_differentiableAt_coeff_prod
-- name    : GlobalTheory.SimpleRoots.differentiableAt_coeff_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:13:06.817863+00:00
-- url     : https://prove2.me/theorems/c48e00d7-e581-4583-8b39-7159fcfa8a57
-- title:
--   Simple Roots: differentiable At coeff prod
-- statement:
--   The Simple Roots construction uses the differentiable At coeff prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L107-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/NodupRootsOfDerivativeNeZero.lean#L107-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_NodupRootsOfDerivativeNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
open GlobalTheory GlobalTheory.SimpleRoots
variable {d : ℕ}

theorem GlobalTheory.SimpleRoots.differentiableAt_coeff_prod {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : Multiset ι) (ψ : ι → E → ℂ) {x₀ : E} (h : ∀ y ∈ T, DifferentiableAt ℂ (ψ y) x₀) (k : ℕ) :
    DifferentiableAt ℂ (fun x => (T.map fun y => X - C (ψ y x)).prod.coeff k) x₀ := by sorry
