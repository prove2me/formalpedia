-- Prove2me | Theorems.Thm_GlobalTheory_AmpCS_ampSq_le_card_mul_sum
-- name    : GlobalTheory.AmpCS.ampSq_le_card_mul_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:45.761308+00:00
-- url     : https://prove2.me/theorems/7092ce75-80f5-5c99-9641-8a55bbc0a709
-- title:
--   Amp CS: amp Sq le card mul sum
-- statement:
--   The Amp CS construction uses the amp Sq le card mul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AmpSqLeCardMulSum.lean#L33-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AmpSqLeCardMulSum.lean#L33-L67

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AmpSqLeCardMulSum
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
open GlobalTheory GlobalTheory.AmpCS
open ValuativeRel MeasureTheory
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.AmpCS.ampSq_le_card_mul_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 1 ≤ k → ∀ {ι : Type} (s : Finset ι) (P : ι → S.Datum → Submodule L.O S.V → Prop) (Q : S.Datum → Submodule L.O S.V → Prop), (∀ d Λ, S.IsTerm d Λ → (Q d Λ ↔ ∃ i ∈ s, P i d Λ)) → (∀ d Λ, S.IsTerm d Λ → ∀ i ∈ s, ∀ i' ∈ s, P i d Λ → P i' d Λ → i = i') → S.ampSq Q ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, S.ampSq (P i) := by sorry
