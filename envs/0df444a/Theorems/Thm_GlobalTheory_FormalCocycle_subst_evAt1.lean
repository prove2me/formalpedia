-- Prove2me | Theorems.Thm_GlobalTheory_FormalCocycle_subst_evAt1
-- name    : GlobalTheory.FormalCocycle.subst_evAt1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:35:12.689749+00:00
-- url     : https://prove2.me/theorems/a06f8118-7642-4c3b-9aff-6a16dea3a6b2
-- title:
--   Formal Cocycle: subst ev At1
-- statement:
--   The Formal Cocycle construction uses the subst ev At1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSeriesSubstPointsStandardThree.lean#L63-L67

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

theorem GlobalTheory.FormalCocycle.subst_evAt1 {b : μ → MvPowerSeries ν k} (hb : HasSubst b)
    {u : Fin d → MvPowerSeries μ k} (hu : Cen u) (f : PS k 1 d) :
    subst b (evAt ![u] f) = evAt ![fun i => subst b (u i)] f := by sorry
