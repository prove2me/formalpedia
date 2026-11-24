-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_expIntegral_nsmul
-- name    : GlobalTheory.FramePull.expIntegral_nsmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:55.365946+00:00
-- url     : https://prove2.me/theorems/0851092a-7007-4da1-8df9-3c048b7d62e2
-- title:
--   Frame Pull: exp Integral nsmul
-- statement:
--   The Frame Pull construction uses the exp Integral nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L239-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L239-L249

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FramePull
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O)
variable {B} {h : PS k 2 d}

theorem GlobalTheory.FramePull.expIntegral_nsmul (hh : B.IsCanonGauge k h) (b c : O) (j : ℕ) :
    ExpIntegral R ((j : k) • ev ![B.actK k b, B.actK k c] h - ev ![B.actK k b, B.actK k ((j : O) * c)] h) := by sorry
