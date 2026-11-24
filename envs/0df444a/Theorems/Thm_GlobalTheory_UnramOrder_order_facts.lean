-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_order_facts
-- name    : GlobalTheory.UnramOrder.order_facts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:17:05.027801+00:00
-- url     : https://prove2.me/theorems/3927128b-bdef-4840-8398-bed7e2305af4
-- title:
--   Unram Order: order facts
-- statement:
--   The Unram Order construction uses the order facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L400-L461
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L400-L461

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
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
open GlobalTheory GlobalTheory.UnramOrder

theorem GlobalTheory.UnramOrder.order_facts : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → (∀ c : 𝒪[F], ∃ x ∈ L.O, x + L.cj x = algebraMap F E c) ∧ (∀ x ∈ L.O, L.cj x ∈ L.O ∧ (∃ c : 𝒪[F], x + L.cj x = algebraMap F E c) ∧ ∃ c : 𝒪[F], x * L.cj x = algebraMap F E c) ∧ (∀ x : E, (∀ b ∈ L.O, ∃ c : 𝒪[F], x * L.cj b + L.cj (x * L.cj b) = algebraMap F E c) → x ∈ L.O) ∧ IsPrincipalIdealRing L.O ∧ (∀ c : F, algebraMap F E c ∈ L.O ↔ c ∈ 𝒪[F]) ∧ (∀ j : ℕ, Nat.card (L.O ⧸ (Ideal.span {y : L.O | (y : E) = algebraMap F E ((ϖ : F) ^ j)})) = resQ ϖ ^ (2 * j)) ∧ 2 ≤ resQ ϖ ∧ (∀ u : (𝒪[F])ˣ, ∃ x ∈ L.O, x * L.cj x = algebraMap F E ((u : 𝒪[F]) : F)) := by sorry
