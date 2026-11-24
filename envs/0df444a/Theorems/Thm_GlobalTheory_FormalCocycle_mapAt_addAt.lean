-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_mapAt_addAt
-- name    : GlobalTheory.FormalCocycle.mapAt_addAt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:33:36.493264+00:00
-- url     : https://prove2.me/theorems/8199585a-05de-4907-ae19-0611507ab829
-- title:
--   Formal Cocycle: map At add At
-- statement:
--   The Formal Cocycle construction uses the map At add At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L133-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L133-L150

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

theorem GlobalTheory.FormalCocycle.mapAt_addAt {ℓ : Pt k 1 d} (hℓ : ∀ i, constantCoeff (ℓ i) = 0)
    {F : Fin d → PS k 2 d} (hF : ∀ i, constantCoeff (F i) = 0)
    (h : comp1 ℓ (addOf F (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1))
    {u v : Fin d → MvPowerSeries μ k} (hu : Cen u) (hv : Cen v) :
    mapAt ℓ (addAt F u v) = mapAt ℓ u + mapAt ℓ v := by sorry
