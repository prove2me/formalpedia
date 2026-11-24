-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryOrbitForm_exists_unitary_mulVec_eq
-- name    : GlobalTheory.UnitaryOrbitForm.exists_unitary_mulVec_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:45:20.397904+00:00
-- url     : https://prove2.me/theorems/ad3c43eb-eea1-4607-bf82-bc51c014c63b
-- title:
--   Unitary Orbit Form: exists unitary mul Vec eq
-- statement:
--   The Unitary Orbit Form construction uses the exists unitary mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L85-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/EqZeroOfEventuallyDotProductStarEqZero.lean#L85-L108

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

theorem GlobalTheory.UnitaryOrbitForm.exists_unitary_mulVec_eq {B : Matrix (Fin r) (Fin r) ℂ} (hB : B.IsHermitian)
    (hdet : B.det ≠ 0) {v w : Fin r → ℂ} (hv : v ≠ 0) (hw : w ≠ 0)
    (h : w ⬝ᵥ B *ᵥ star w = v ⬝ᵥ B *ᵥ star v) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᵀ * B * g.map (starRingEnd ℂ) = B ∧ g *ᵥ v = w := by sorry
