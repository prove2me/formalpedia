-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_LatForm_exists_dvd_coprime_mul_pow
-- name    : GlobalTheory.UnRep.LatForm.exists_dvd_coprime_mul_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:27.642505+00:00
-- url     : https://prove2.me/theorems/cfecfe3a-6c9e-4600-a33d-87d330fb37ff
-- title:
--   Lat Form: exists dvd coprime mul pow
-- statement:
--   The Lat Form construction uses the exists dvd coprime mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L14-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitaryCorrectionCongruentOneAtLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalUnitarySplitDenominator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.LatForm
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors

theorem GlobalTheory.UnRep.LatForm.exists_dvd_coprime_mul_pow (N : ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ j u : ℕ, u.Coprime N ∧ m ∣ u * N ^ j := by sorry
