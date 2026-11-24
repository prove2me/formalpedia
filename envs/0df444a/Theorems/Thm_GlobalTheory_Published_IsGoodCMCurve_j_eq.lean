-- Prove2me | Theorems.Thm_GlobalTheory_Published_IsGoodCMCurve_j_eq
-- name    : GlobalTheory.Published.IsGoodCMCurve.j_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:56:05.804243+00:00
-- url     : https://prove2.me/theorems/99fd8168-3db5-40a9-bb6b-d071f9e380cb
-- title:
--   Is Good CMCurve: j eq
-- statement:
--   The Is Good CMCurve construction uses the j eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L217-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L217-L220

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

theorem GlobalTheory.Published.IsGoodCMCurve.j_eq [A.IsElliptic] (h : IsGoodCMCurve p F A) {L : PeriodPair}
    (hL : IsIntegersLattice p L) : (A.j : ℂ) = (latticeCurve L).j := by sorry
