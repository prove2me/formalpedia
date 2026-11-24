-- Prove2me | Theorems.Thm_GlobalTheory_Published_isTotallyComplex_of_sq_eq_neg
-- name    : GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:12:36.617026+00:00
-- url     : https://prove2.me/theorems/93356024-f3f9-4115-bed4-6f20e03367d5
-- title:
--   Published: is Totally Complex of sq eq neg
-- statement:
--   The Published construction uses the is Totally Complex of sq eq neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L65-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__CmCurveGoodOutsidePrimePremises_e87ddea43482082e
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain WeierstrassCurve
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {p : ℕ} {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Published.isTotallyComplex_of_sq_eq_neg (hp : 0 < p) {x : K} (hx : x ^ 2 = -(p : K)) :
    IsTotallyComplex K := by sorry
