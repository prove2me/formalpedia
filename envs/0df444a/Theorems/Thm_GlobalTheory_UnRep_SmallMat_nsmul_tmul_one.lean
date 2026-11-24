-- Prove2me | Theorems.Thm_GlobalTheory_UnRep_SmallMat_nsmul_tmul_one
-- name    : GlobalTheory.UnRep.SmallMat.nsmul_tmul_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:21:28.511119+00:00
-- url     : https://prove2.me/theorems/17f4c2d5-1158-4565-bc96-cd70eeed2b6f
-- title:
--   Small Mat: nsmul tmul one
-- statement:
--   The Small Mat construction uses the nsmul tmul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IdempotentAdelesAndSmallAdelicMatrices.lean#L92-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatrices
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
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.SmallMat
open GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.UnRep.SmallMat.nsmul_tmul_one (d : ℕ) (a : FiniteAdeleRing (𝓞 F) F) :
    ((d • a) ⊗ₜ[F] (1 : E) : RA F E) = d • (a ⊗ₜ[F] (1 : E) : RA F E) := by sorry
