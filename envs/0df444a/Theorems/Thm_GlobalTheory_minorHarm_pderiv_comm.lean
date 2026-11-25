-- Prove2me | Theorems.Thm_GlobalTheory_minorHarm_pderiv_comm
-- name    : GlobalTheory.minorHarm_pderiv_comm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:50.726318+00:00
-- url     : https://prove2.me/theorems/aaf75681-52f4-4560-836b-04645b8ce0b9
-- title:
--   Global Theory: minor Harm pderiv comm
-- statement:
--   The Global Theory construction uses the minor Harm pderiv comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MinorsDisjointColumnsHarmonic.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MinorsDisjointColumnsHarmonic.lean#L9-L22

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

theorem GlobalTheory.minorHarm_pderiv_comm {σ k : Type*} [CommRing k] (i j : σ)
    (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by sorry
