-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_germ_ev_ev_single_point_comp
-- name    : GlobalTheory.FramePull.germ_ev_ev_single_point_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:50.052815+00:00
-- url     : https://prove2.me/theorems/1cf1dc64-34c9-478e-84a8-23d2a3122d24
-- title:
--   Frame Pull: germ ev ev single point comp
-- statement:
--   The Frame Pull construction uses the germ ev ev single point comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L72-L77

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
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.FramePull.germ_ev_ev_single_point_comp {n l : ℕ} {x : Pt R n d} {b : Fin n → Pt R l d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R 1 d) :
    ev b (ev ![x] f) = ev ![fun i => ev b (x i)] f := by sorry
