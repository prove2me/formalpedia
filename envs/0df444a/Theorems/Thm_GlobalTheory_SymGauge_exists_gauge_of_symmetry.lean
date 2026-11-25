-- Prove2me | Theorems.Thm_GlobalTheory_SymGauge_exists_gauge_of_symmetry
-- name    : GlobalTheory.SymGauge.exists_gauge_of_symmetry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:23:53.149803+00:00
-- url     : https://prove2.me/theorems/36427086-dfa7-4e81-900e-1669859d8dc1
-- title:
--   Sym Gauge: exists gauge of symmetry
-- statement:
--   The Sym Gauge construction uses the exists gauge of symmetry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGaugeOfSymmetry.lean#L30-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGaugeOfSymmetry.lean#L30-L110

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGaugeOfSymmetry
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
open GlobalTheory GlobalTheory.SymGauge
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.SymGauge.exists_gauge_of_symmetry :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) := by sorry
