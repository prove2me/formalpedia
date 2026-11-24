-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_cocycle_at
-- name    : GlobalTheory.FormalCocycle.cocycle_at
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:29.41654+00:00
-- url     : https://prove2.me/theorems/09921e44-3afb-433a-81e6-afdd22084e9a
-- title:
--   Formal Cocycle: cocycle at
-- statement:
--   The Formal Cocycle construction uses the cocycle at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L179-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L179-L200

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

theorem GlobalTheory.FormalCocycle.cocycle_at {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0) {c : PS k 3 d}
    (h : ev (n := 4) ![pt k d 0, pt k d 1, pt k d 3] c +
        ev (n := 4) ![addOf F (pt k d 0) (pt k d 1), pt k d 2, pt k d 3] c =
      ev (n := 4) ![pt k d 1, pt k d 2, pt k d 3] c +
        ev (n := 4) ![pt k d 0, addOf F (pt k d 1) (pt k d 2), pt k d 3] c)
    {u v w t : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) (hw : Cen w) (ht : Cen t) :
    evAt ![u, v, t] c + evAt ![addAt F u v, w, t] c =
      evAt ![v, w, t] c + evAt ![u, addAt F v w, t] c := by sorry
