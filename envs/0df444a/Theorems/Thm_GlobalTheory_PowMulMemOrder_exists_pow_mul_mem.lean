-- Prove2me | Theorems.Thm_GlobalTheory_PowMulMemOrder_exists_pow_mul_mem
-- name    : GlobalTheory.PowMulMemOrder.exists_pow_mul_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:47:13.224649+00:00
-- url     : https://prove2.me/theorems/c9406f21-4ca0-5e44-88ba-5bbc7380fd9a
-- title:
--   Pow Mul Mem Order: exists pow mul mem
-- statement:
--   The Pow Mul Mem Order construction uses the exists pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisFurther.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ImportsBisFurther.lean#L14-L30

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ImportsBisFurther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.PowMulMemOrder
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.PowMulMemOrder.exists_pow_mul_mem (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (c : E) :
    ∃ k : ℕ, algebraMap F E ((ϖ : F) ^ k) * c ∈ L.O := by sorry
