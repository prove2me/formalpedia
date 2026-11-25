-- Prove2me | Theorems.Thm_GlobalTheory_GaugeSecondDeriv_ev_pderiv_add
-- name    : GlobalTheory.GaugeSecondDeriv.ev_pderiv_add
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:30.121131+00:00
-- url     : https://prove2.me/theorems/ce9e68f6-e34d-4ac3-af0d-7c0645132dab
-- title:
--   Gauge Second Deriv: ev pderiv add
-- statement:
--   The Gauge Second Deriv construction uses the ev pderiv add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PderivEvSecond.lean#L26-L38

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

theorem GlobalTheory.GaugeSecondDeriv.ev_pderiv_add (F : PS k 2 d) (b : Fin d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0]
      (pderiv k ((2 : Fin 3), b) (ev (n := 3) ![pt k d 1, pt k d 2] F)) =
      ev (n := 2) ![pt k d 1, 0] (pderiv k ((1 : Fin 2), b) F) := by sorry
