-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_LatForm_one_tmul_natCast_mul_smul
-- name    : GlobalTheory.UnRep.LatForm.one_tmul_natCast_mul_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:54.295257+00:00
-- url     : https://prove2.me/theorems/bf11f7fa-00ce-406b-8bc8-d9b06be6a353
-- title:
--   Lat Form: one tmul nat Cast mul smul
-- statement:
--   The Lat Form construction uses the one tmul nat Cast mul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L172-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsRationalUnitarySplitDenominator.lean#L172-L176

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

theorem GlobalTheory.UnRep.LatForm.one_tmul_natCast_mul_smul (m : ℕ) (s : 𝓞 E) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((((m : 𝓞 E) * s : 𝓞 E)) : E)) • z =
      m • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z := by sorry
