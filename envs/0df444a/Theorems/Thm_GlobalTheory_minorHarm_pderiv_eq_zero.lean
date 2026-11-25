-- Prove2me | Theorems.Thm_GlobalTheory_minorHarm_pderiv_eq_zero
-- name    : GlobalTheory.minorHarm_pderiv_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:44:23.833603+00:00
-- url     : https://prove2.me/theorems/72cdb7ee-66e8-4692-8caf-848fcd12e51a
-- title:
--   Global Theory: minor Harm pderiv eq zero
-- statement:
--   The Global Theory construction uses the minor Harm pderiv eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MinorsDisjointColumnsHarmonic.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MinorsDisjointColumnsHarmonic.lean#L26-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open MvPowerSeries

theorem GlobalTheory.minorHarm_pderiv_eq_zero {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) {v : σ} (hv : v ∉ S) :
    MvPolynomial.pderiv v p = 0 := by sorry
