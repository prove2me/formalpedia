-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryOrbitForm_eq_zero_of_forall_dotProduct_star_eq_zero
-- name    : GlobalTheory.UnitaryOrbitForm.eq_zero_of_forall_dotProduct_star_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:57.563435+00:00
-- url     : https://prove2.me/theorems/a9a0be56-9df7-4f84-9c4c-6158c9028638
-- title:
--   Unitary Orbit Form: eq zero of forall dot Product star eq zero
-- statement:
--   The Unitary Orbit Form construction uses the eq zero of forall dot Product star eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L18-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L18-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfEventuallyDotProductStarEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitaryOrbitForm
open Matrix Filter Topology
variable {r : ℕ}

theorem GlobalTheory.UnitaryOrbitForm.eq_zero_of_forall_dotProduct_star_eq_zero {C : Matrix (Fin r) (Fin r) ℂ}
    (h : ∀ u : Fin r → ℂ, u ⬝ᵥ C *ᵥ star u = 0) : C = 0 := by sorry
