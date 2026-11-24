-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_LatForm_congAtA_mul
-- name    : GlobalTheory.UnRep.LatForm.congAtA_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:23:59.420803+00:00
-- url     : https://prove2.me/theorems/5de1ee29-998e-46db-95d9-ec331e9afe18
-- title:
--   Lat Form: cong At A mul
-- statement:
--   The Lat Form construction uses the cong At A mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L133-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L133-L146

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.UnRep.LatForm.congAtA_mul (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : CongAtA F L N D a) (hb : CongAtA F L N D b) : CongAtA F L N D (a * b) := by sorry
