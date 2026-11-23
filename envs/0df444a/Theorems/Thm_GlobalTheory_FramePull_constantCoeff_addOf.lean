-- Prove2me | Theorems.Thm_GlobalTheory_FramePull_constantCoeff_addOf
-- name    : GlobalTheory.FramePull.constantCoeff_addOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:55:57.010319+00:00
-- url     : https://prove2.me/theorems/7a5009ba-5591-4990-8f7b-b6ce9b76862e
-- title:
--   Frame Pull: constant Coeff add Of
-- statement:
--   The Frame Pull construction uses the constant Coeff add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PowerSeriesExpIntegralCanonGaugeAdditiveSecond.lean#L104-L107

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

theorem GlobalTheory.FramePull.constantCoeff_addOf {n : ℕ} {F : Fin d → PS R 2 d} {x y : Pt R n d} (hF : ∀ i, constantCoeff (F i) = 0)
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0) (i : Fin d) :
    constantCoeff (addOf F x y i) = 0 := by sorry
