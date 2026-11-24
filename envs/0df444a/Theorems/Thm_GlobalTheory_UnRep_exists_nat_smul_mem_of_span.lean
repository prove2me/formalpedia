-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_exists_nat_smul_mem_of_span
-- name    : GlobalTheory.UnRep.exists_nat_smul_mem_of_span
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:24:45.251677+00:00
-- url     : https://prove2.me/theorems/64e91c14-75d1-4e98-9a13-a92856de6ca6
-- title:
--   Un Rep: exists nat smul mem of span
-- statement:
--   The Un Rep construction uses the exists nat smul mem of span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormOneReflectionCorrectionAtLevel.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNormOneReflectionCorrectionAtLevel.lean#L23-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNatSmulMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPosNatMulMemRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNormOneReflectionCorrectionAtLevel
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

theorem GlobalTheory.UnRep.exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by sorry
