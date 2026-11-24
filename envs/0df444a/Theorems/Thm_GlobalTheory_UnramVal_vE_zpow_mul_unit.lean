-- Prove2me | Theorems.Thm_GlobalTheory_UnramVal_vE_zpow_mul_unit
-- name    : GlobalTheory.UnramVal.vE_zpow_mul_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:47:05.779796+00:00
-- url     : https://prove2.me/theorems/9d72af3a-e235-4469-9926-9b8eb61bc49c
-- title:
--   Unram Val: v E zpow mul unit
-- statement:
--   The Unram Val construction uses the v E zpow mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L37-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L37-L55

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramVal
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]

theorem GlobalTheory.UnramVal.vE_zpow_mul_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ)
    (u : (𝒪[F])ˣ) : vE L ϖ (algebraMap F E ((ϖ : F) ^ k * ((u : 𝒪[F]) : F))) = k := by sorry
