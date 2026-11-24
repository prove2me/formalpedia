-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_cen_X
-- name    : GlobalTheory.FormalCocycle.cen_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:33:37.296317+00:00
-- url     : https://prove2.me/theorems/c70b1c85-773e-4065-b95a-8333b2f2ea2e
-- title:
--   Formal Cocycle: cen X
-- statement:
--   The Formal Cocycle construction uses the cen X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L43-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L43-L43

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

theorem GlobalTheory.FormalCocycle.cen_X (g : Fin d → μ) : Cen (fun i => (X (g i) : MvPowerSeries μ k)) := by sorry
