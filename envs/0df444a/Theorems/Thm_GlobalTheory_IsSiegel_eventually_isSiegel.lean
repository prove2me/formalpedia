-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_eventually_isSiegel
-- name    : GlobalTheory.IsSiegel.eventually_isSiegel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:43.563942+00:00
-- url     : https://prove2.me/theorems/49de52b0-0eae-40da-92e3-bb1b446f892a
-- title:
--   Is Siegel: eventually is Siegel
-- statement:
--   The Is Siegel construction uses the eventually is Siegel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L206-L212

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_PeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι κ : Type*}
variable [Fintype ι] [Fintype κ]

theorem GlobalTheory.IsSiegel.eventually_isSiegel {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∀ᶠ Ω' in 𝓝 Ω, Matrix.IsSymm Ω' → IsSiegel Ω' := by sorry
