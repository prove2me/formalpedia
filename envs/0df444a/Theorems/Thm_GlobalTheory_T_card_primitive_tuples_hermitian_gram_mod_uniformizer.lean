-- Prove2me | Theorems.Thm_GlobalTheory_T_card_primitive_tuples_hermitian_gram_mod_uniformizer
-- name    : GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:47.754416+00:00
-- url     : https://prove2.me/theorems/790fbbf4-f63b-4142-8b75-8cf91acda039
-- title:
--   T: card primitive tuples hermitian gram mod uniformizer
-- statement:
--   The T construction uses the card primitive tuples hermitian gram mod uniformizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTuplesHermitianGramModUniformizerStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTuplesHermitianGramModUniformizerStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizerStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_primitive_tuples_hermitian_gram_mod_uniformizer : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (n m j : ℕ), 2 * m + 3 ≤ n → 1 ≤ j → ∀ (Gm : Matrix (Fin m) (Fin m) E), IsHerm L Gm → IsIntM L Gm → ∀ (R : Finset E), (∀ u ∈ R, u ∈ L.O) → (∀ u ∈ L.O, ∃! w, w ∈ R ∧ ∃ c ∈ L.O, u - w = algebraMap F E ((ϖ : F) ^ j) * c) → ∀ N : ℕ, N = Set.ncard {x : Fin m → Fin n → E | (∀ a i, x a i ∈ R) ∧ (∃ y : Fin m → Fin n → E, (∀ a i, y a i ∈ L.O) ∧ ∀ a b, hf L 1 (x a) (y b) = if a = b then 1 else 0) ∧ ∀ a b, ∃ c ∈ L.O, hf L 1 (x b) (x a) - Gm a b = algebraMap F E ((ϖ : F) ^ j) * c} → (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) ≤ 2 * N ∧ (N : ℝ) ≤ 2 * (resQ ϖ : ℝ) ^ (j * (2 * n * m - m ^ 2)) := by sorry
