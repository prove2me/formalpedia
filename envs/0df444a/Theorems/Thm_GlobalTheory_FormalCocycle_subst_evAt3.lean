-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt3
-- name    : GlobalTheory.FormalCocycle.subst_evAt3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:25.744459+00:00
-- url     : https://prove2.me/theorems/fe5e9edb-8805-4047-a69c-e89c572aaf1b
-- title:
--   Formal Cocycle: subst ev At3
-- statement:
--   The Formal Cocycle construction uses the subst ev At3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L75-L80

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

theorem GlobalTheory.FormalCocycle.subst_evAt3 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u v w : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (f : PS k 3 d) :
    subst b (evAt ![u, v, w] f) =
      evAt ![fun i => subst b (u i), fun i => subst b (v i), fun i => subst b (w i)] f := by sorry
