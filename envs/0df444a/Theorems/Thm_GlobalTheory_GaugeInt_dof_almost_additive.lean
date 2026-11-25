-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_dof_almost_additive
-- name    : GlobalTheory.GaugeInt.dof_almost_additive
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:54.359796+00:00
-- url     : https://prove2.me/theorems/7d7fca13-58fe-4f95-bb74-a75df1fc4ada
-- title:
--   Gauge Int: dof almost additive
-- statement:
--   The Gauge Int construction uses the dof almost additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L118-L124

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
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
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}

theorem GlobalTheory.GaugeInt.dof_almost_additive {F : Pt k 2 d} (hF : GP F)
    (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    (f : PS k 1 d)
    (hf : ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f - ev ![F] f ∈ IntS φ 2 d) :
    Dof F v f - C (lin v f) ∈ IntS φ 1 d := by sorry
