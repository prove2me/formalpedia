-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsGoodCMCurve_field_eq
-- name    : GlobalTheory.Published.IsGoodCMCurve.field_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:37.014977+00:00
-- url     : https://prove2.me/theorems/38c26681-df86-4bcf-8f5e-67909cefb534
-- title:
--   Is Good CMCurve: field eq
-- statement:
--   The Is Good CMCurve construction uses the field eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L222-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L222-L225

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

theorem GlobalTheory.Published.IsGoodCMCurve.field_eq (h : IsGoodCMCurve p F A) {L : PeriodPair}
    (hL : IsIntegersLattice p L) : F = ℚ⟮(latticeCurve L).j⟯ := by sorry
