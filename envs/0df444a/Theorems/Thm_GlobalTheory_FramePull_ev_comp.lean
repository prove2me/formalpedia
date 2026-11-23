-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_ev_comp
-- name    : GlobalTheory.FramePull.ev_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:59.965412+00:00
-- url     : https://prove2.me/theorems/d6013016-babe-41b4-baf5-c6469df096ce
-- title:
--   Frame Pull: ev comp
-- statement:
--   The Frame Pull construction uses the ev comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L21-L25

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

theorem GlobalTheory.FramePull.ev_comp {n m l : ℕ} {a : Fin m → Pt R n d} {b : Fin n → Pt R l d}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by sorry
