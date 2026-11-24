-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_ev_comp1
-- name    : GlobalTheory.FramePull.ev_comp1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:39.404573+00:00
-- url     : https://prove2.me/theorems/48317c99-923f-42f3-8ba1-1b90b6791b3c
-- title:
--   Frame Pull: ev comp1
-- statement:
--   The Frame Pull construction uses the ev comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L89-L92

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

theorem GlobalTheory.FramePull.ev_comp1 {n l : ℕ} (φ : Pt R 1 d) {x : Pt R n d} {b : Fin n → Pt R l d}
    (hx : ∀ i, constantCoeff (x i) = 0) (hb : ∀ j i, constantCoeff (b j i) = 0) :
    (fun i => ev b (comp1 φ x i)) = comp1 φ (fun i => ev b (x i)) := by sorry
