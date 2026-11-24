-- Prove2me | Theorems.Thm_GlobalTheory_ActionGauge_exists_action_gauge
-- name    : GlobalTheory.ActionGauge.exists_action_gauge
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:53:55.536934+00:00
-- url     : https://prove2.me/theorems/449f9eb9-4b74-49bc-8147-c4edd930cd68
-- title:
--   Action Gauge: exists action gauge
-- statement:
--   The Action Gauge construction uses the exists action gauge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsActionGauge.lean#L321-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsActionGauge.lean#L321-L332

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

theorem GlobalTheory.ActionGauge.exists_action_gauge :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) := by sorry
