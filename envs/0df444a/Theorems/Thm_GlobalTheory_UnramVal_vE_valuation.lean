-- Prove2me | Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- name    : GlobalTheory.UnramVal.vE_valuation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:38.346562+00:00
-- url     : https://prove2.me/theorems/a4de3353-937f-48b9-9603-f7a2a80e6cd6
-- title:
--   Unram Val: v E valuation
-- statement:
--   The Unram Val construction uses the v E valuation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsEqZpowMulUnit.lean#L63-L77

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

theorem GlobalTheory.UnramVal.vE_valuation : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ x y : F, x ≠ 0 → y ≠ 0 → vE L ϖ (algebraMap F E (x * y)) = vE L ϖ (algebraMap F E x) + vE L ϖ (algebraMap F E y)) ∧ vE L ϖ (algebraMap F E (ϖ : F)) = 1 ∧ (∀ x : F, x ≠ 0 → (0 ≤ vE L ϖ (algebraMap F E x) ↔ x ∈ 𝒪[F])) ∧ (∀ x : F, x ≠ 0 → ∃ u : (𝒪[F])ˣ, x = (ϖ : F) ^ (vE L ϖ (algebraMap F E x)) * ((u : 𝒪[F]) : F)) := by sorry
