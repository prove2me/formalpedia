-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsGoodCMCurve_hasGoodReductionOutside
-- name    : GlobalTheory.Published.IsGoodCMCurve.hasGoodReductionOutside
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:16:27.399176+00:00
-- url     : https://prove2.me/theorems/9ae3bd36-b026-50d5-b387-93d9f7615ed0
-- title:
--   Is Good CMCurve: has Good Reduction Outside
-- statement:
--   The Is Good CMCurve construction uses the has Good Reduction Outside property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L212-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L212-L215

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
variable {p : ℕ}
variable {F : IntermediateField ℚ ℂ} {A : WeierstrassCurve F}

theorem GlobalTheory.Published.IsGoodCMCurve.hasGoodReductionOutside [NumberField F] (h : IsGoodCMCurve p F A) :
    HasGoodReductionOutside p A := by sorry
