-- Prove2me | Theorems.Thm_GlobalTheory_HL_NormalFormRescaled_alg_inv_mul
-- name    : GlobalTheory.HL.NormalFormRescaled.alg_inv_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:51:43.049479+00:00
-- url     : https://prove2.me/theorems/e78df880-7881-5431-8aff-9ead3364a3e9
-- title:
--   Normal Form Rescaled: alg inv mul
-- statement:
--   The Normal Form Rescaled construction uses the alg inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFlagUnipotentNormalFormRescaled.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFlagUnipotentNormalFormRescaled.lean#L27-L28

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFlagUnipotentNormalFormRescaled
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.NormalFormRescaled
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
omit [TopologicalSpace E]

theorem GlobalTheory.HL.NormalFormRescaled.alg_inv_mul (a : Fˣ) : algebraMap F E ((a⁻¹ : Fˣ) : F) * algebraMap F E (a : F) = 1 := by sorry
