-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_expIntegral_ev
-- name    : GlobalTheory.FramePull.expIntegral_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:58.656453+00:00
-- url     : https://prove2.me/theorems/d9da6627-635e-4ef4-833d-27fa769d7e77
-- title:
--   Frame Pull: exp Integral ev
-- statement:
--   The Frame Pull construction uses the exp Integral ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L144-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L144-L153

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
variable (R : Type) [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {R}

theorem GlobalTheory.FramePull.expIntegral_ev {m : ℕ} {a : Fin m → Pt R 1 d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    {w : PS R m d} (w1 : constantCoeff w = 1) {f : PS k m d} (f0 : constantCoeff f = 0)
    (hw : FB.toK k w = FB.expS k f) :
    ExpIntegral R (ev (fun j i => FB.toK k (a j i)) f) := by sorry
