-- Prove2me | Theorems.Thm_GlobalTheory_GaugeSecondDeriv_pderiv_ev_second
-- name    : GlobalTheory.GaugeSecondDeriv.pderiv_ev_second
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:38.929409+00:00
-- url     : https://prove2.me/theorems/1a01bffa-9e22-4afe-8d77-e5d38df9b3ef
-- title:
--   Gauge Second Deriv: pderiv ev second
-- statement:
--   The Gauge Second Deriv construction uses the pderiv ev second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L19-L24

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

theorem GlobalTheory.GaugeSecondDeriv.pderiv_ev_second (h : PS k 2 d) (q : Pt k 3 d) (hq : ∀ c, constantCoeff (q c) = 0) (b : Fin d) :
    pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 0, q] h) =
      ∑ j, ev (n := 3) ![pt k d 0, q] (pderiv k ((1 : Fin 2), j) h) * pderiv k ((2 : Fin 3), b) (q j) := by sorry
