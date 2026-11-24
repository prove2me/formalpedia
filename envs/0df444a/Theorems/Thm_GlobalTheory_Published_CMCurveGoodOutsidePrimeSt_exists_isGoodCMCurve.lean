-- Prove2me | Theorems.Thm_GlobalTheory_Published_CMCurveGoodOutsidePrimeSt_exists_isGoodCMCurve
-- name    : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt.exists_isGoodCMCurve
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T18:57:10.694396+00:00
-- url     : https://prove2.me/theorems/aa5d4f26-64ee-4b47-a16f-7f3d5b235d2c
-- title:
--   CMCurve Good Outside Prime St: exists is Good CMCurve
-- statement:
--   The CMCurve Good Outside Prime St construction uses the exists is Good CMCurve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L227-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/CmCurveGoodOutsidePrimePremises.lean#L227-L231

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

theorem GlobalTheory.Published.CMCurveGoodOutsidePrimeSt.exists_isGoodCMCurve (h : CMCurveGoodOutsidePrimeSt)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) :
    ∃ (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F), IsGoodCMCurve p F A := by sorry
