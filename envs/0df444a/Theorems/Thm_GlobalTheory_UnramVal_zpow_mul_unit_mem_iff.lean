-- Prove2me | Theorems.Thm_GlobalTheory_UnramVal_zpow_mul_unit_mem_iff
-- name    : GlobalTheory.UnramVal.zpow_mul_unit_mem_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:12.614052+00:00
-- url     : https://prove2.me/theorems/7c23b5f1-5c31-40c8-9dea-9875595cfeed
-- title:
--   Unram Val: zpow mul unit mem iff
-- statement:
--   The Unram Val construction uses the zpow mul unit mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L14-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L14-L33

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

theorem GlobalTheory.UnramVal.zpow_mul_unit_mem_iff {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (k : ℤ) (u : (𝒪[F])ˣ) :
    (ϖ : F) ^ k * ((u : 𝒪[F]) : F) ∈ 𝒪[F] ↔ 0 ≤ k := by sorry
