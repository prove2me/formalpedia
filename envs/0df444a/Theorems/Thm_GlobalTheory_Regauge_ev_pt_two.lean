-- Prove2me | Theorems.Thm_GlobalTheory_Regauge_ev_pt_two
-- name    : GlobalTheory.Regauge.ev_pt_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:36:35.069802+00:00
-- url     : https://prove2.me/theorems/296e16cc-1fd1-4322-a52c-2ff14004e694
-- title:
--   Regauge: ev pt two
-- statement:
--   The Regauge construction uses the ev pt two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvRegaugedSecondLawFamily.lean#L23-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvRegaugedSecondLawFamily.lean#L23-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.Regauge
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.Regauge.ev_pt_two (f : PS k 2 d) : ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] f = f := by sorry
