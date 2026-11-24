-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_card_quot_eq_sq
-- name    : GlobalTheory.UnramOrder.card_quot_eq_sq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:46:46.809808+00:00
-- url     : https://prove2.me/theorems/2d9ea20b-3e42-4649-a6ec-ab087564fc73
-- title:
--   Unram Order: card quot eq sq
-- statement:
--   The Unram Order construction uses the card quot eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L30-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L30-L71

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
open IsLocalRing Polynomial
variable {R₀ R : Type*} [CommRing R₀] [CommRing R] [Algebra R₀ R]

theorem GlobalTheory.UnramOrder.card_quot_eq_sq (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hinj : Function.Injective (algebraMap R₀ R))
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω)) (p : R₀) :
    Nat.card (R ⧸ Ideal.span {algebraMap R₀ R p}) = Nat.card (R₀ ⧸ Ideal.span {p}) ^ 2 := by sorry
