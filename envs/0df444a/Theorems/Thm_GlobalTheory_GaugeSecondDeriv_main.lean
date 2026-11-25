-- Prove2me | Theorems.Thm_GlobalTheory_GaugeSecondDeriv_main
-- name    : GlobalTheory.GaugeSecondDeriv.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:49.47231+00:00
-- url     : https://prove2.me/theorems/344c1ea6-52c5-473b-a16e-c096f47da7e5
-- title:
--   Gauge Second Deriv: main
-- statement:
--   The Gauge Second Deriv construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L52-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L52-L99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_IntegralFamilyFirstZeroSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeSecondDeriv
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.GaugeSecondDeriv.main : (∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), B.IsCanonGauge k h → ∀ b : Fin d, ∃ K : PS R 2 d, ∑ j, ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) (B.FK k j)) * pderiv k ((1 : Fin 2), j) h =
    FB.toK k K + ev (n := 2) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) h)) := by sorry
