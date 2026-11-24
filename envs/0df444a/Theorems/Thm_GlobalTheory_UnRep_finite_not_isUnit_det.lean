-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_finite_not_isUnit_det
-- name    : GlobalTheory.UnRep.finite_not_isUnit_det
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:03.192154+00:00
-- url     : https://prove2.me/theorems/cdeb9578-a500-4a06-ba93-c479ab1b8aa4
-- title:
--   Un Rep: finite not is Unit det
-- statement:
--   The Un Rep construction uses the finite not is Unit det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L33-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/AdelicUnitaryScalingUnit.lean#L33-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneInfinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep

theorem GlobalTheory.UnRep.finite_not_isUnit_det {E R : Type} [Field E] [CommRing R] (φ : E →+* R) {n : ℕ}
    (g : Matrix (Fin n) (Fin n) R) (ε : R) (hε : ε * ε = ε)
    (hfin : {M : Ideal R | M.IsMaximal ∧ 1 - ε ∈ M}.Finite) :
    {l : E | ¬ IsUnit (1 + φ l • (ε • g + (1 - ε) • (1 : Matrix (Fin n) (Fin n) R))).det}.Finite := by sorry
