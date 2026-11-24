-- Prove2me | Theorems.Thm_GlobalTheory_canonGauge_of_steps
-- name    : GlobalTheory.canonGauge_of_steps
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:45.784594+00:00
-- url     : https://prove2.me/theorems/4f3e8ad6-7ae0-4a6f-a504-8f7146a51f77
-- title:
--   Global Theory: canon Gauge of steps
-- statement:
--   The Global Theory construction uses the canon Gauge of steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeOfSteps.lean#L73-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeOfSteps.lean#L73-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
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
open GlobalTheory.CanonGaugeAssembly

theorem GlobalTheory.canonGauge_of_steps :
    (∀ (R k : Type) [CommRing R] [CommRing k] (f : R →+* k) (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ B' : FB k d O, (∀ i, B'.G.F i = MvPowerSeries.map f (B.G.F i)) ∧ (∀ a i, B'.A.act a i = MvPowerSeries.map f (B.A.act a i)) ∧ B'.ph1 = MvPowerSeries.map f B.ph1 ∧ B'.ph2 = MvPowerSeries.map f B.ph2 ∧ B'.sy = MvPowerSeries.map f B.sy ∧ ∀ a, B'.ad a = MvPowerSeries.map f (B.ad a)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O) (h : PS k 2 d), (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) → ∃ B' : FB k d O, B'.G.F = B.G.F ∧ B'.A.act = B.A.act ∧ B.ph1 = B'.ph1 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) ∧ B.ph2 = B'.ph2 * FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) ∧ B.sy = B'.sy * FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h) ∧ ∀ a : O, B.ad a = B'.ad a * FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ B.ph1 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ B.ph2 = FB.expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h)) → (∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → (∀ a, B.ad a = 1) → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ (∀ a : O, (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) = 0) ∧ B.sy = FB.expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)) → CanonGaugeSt := by sorry
