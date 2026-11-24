-- Prove2me | Theorems.Thm_GlobalTheory_UnramOrder_isPrincipalIdealRing_of_henselian
-- name    : GlobalTheory.UnramOrder.isPrincipalIdealRing_of_henselian
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:47:03.814276+00:00
-- url     : https://prove2.me/theorems/06a41c82-4a6f-49b3-a8b8-54bf2f0d92a6
-- title:
--   Unram Order: is Principal Ideal Ring of henselian
-- statement:
--   The Unram Order construction uses the is Principal Ideal Ring of henselian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L73-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IsPrincipalIdealRingOfHenselian.lean#L73-L194

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

theorem GlobalTheory.UnramOrder.isPrincipalIdealRing_of_henselian [IsDomain R₀] [IsDiscreteValuationRing R₀]
    [HenselianRing R₀ (maximalIdeal R₀)] (c : R →+* R) (hc : ∀ x, c (c x) = x)
    (hbase : ∀ r, c (algebraMap R₀ R r) = algebraMap R₀ R r)
    (hfix : ∀ x, c x = x → x ∈ (algebraMap R₀ R).range) {ω : R} (hω : IsUnit (ω - c ω))
    (hD : ∀ r : R₀, IsUnit (algebraMap R₀ R r) → IsUnit r) :
    IsPrincipalIdealRing R := by sorry
