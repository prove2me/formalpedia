-- Prove2me | Theorems.Thm_GlobalTheory_ActionGauge_logAd_mul
-- name    : GlobalTheory.ActionGauge.logAd_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:54:15.149022+00:00
-- url     : https://prove2.me/theorems/2aa99245-d9bc-44f2-986a-3c3bf72a505b
-- title:
--   Action Gauge: log Ad mul
-- statement:
--   The Action Gauge construction uses the log Ad mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsActionGauge.lean#L306-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsActionGauge.lean#L306-L317

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
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
open GlobalTheory GlobalTheory.ActionGauge
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
  (B : FB k d O)

theorem GlobalTheory.ActionGauge.logAd_mul (a b : O) : logAd B (a * b) =
    ev ![comp1 (B.A.act b) (pt k (n := 2) d 0), pt k (n := 2) d 1] (logAd B a) +
      ev ![pt k (n := 2) d 0, comp1 (B.A.act (star a)) (pt k (n := 2) d 1)] (logAd B b) := by sorry
