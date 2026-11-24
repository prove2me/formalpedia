-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt2
-- name    : GlobalTheory.FormalCocycle.subst_evAt2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:34:54.671239+00:00
-- url     : https://prove2.me/theorems/2d3f6973-4a79-4ade-9c78-3babc79e4b75
-- title:
--   Formal Cocycle: subst ev At2
-- statement:
--   The Formal Cocycle construction uses the subst ev At2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L69-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSeriesSubstPointsStandardThree
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Sum
open GlobalTheory GlobalTheory.FormalCocycle
variable {k : Type} [CommRing k] {d : ℕ} {μ ν : Type}

theorem GlobalTheory.FormalCocycle.subst_evAt2 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (f : PS k 2 d) :
    subst b (evAt ![u, v] f) = evAt ![fun i => subst b (u i), fun i => subst b (v i)] f := by sorry
