-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_norm_riemannThetaTerm_le
-- name    : GlobalTheory.IsSiegel.exists_eventually_norm_riemannThetaTerm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:36.845953+00:00
-- url     : https://prove2.me/theorems/f4af254d-2bc2-43f4-a6f8-d14f9837ec8b
-- title:
--   Is Siegel: exists eventually norm riemann Theta Term le
-- statement:
--   The Is Siegel construction uses the exists eventually norm riemann Theta Term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L359-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L359-L367

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

theorem GlobalTheory.IsSiegel.exists_eventually_norm_riemannThetaTerm_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω)
    (a b : ι → ℝ) (v : ι → ℂ) : ∃ c > 0, ∃ S, ∀ᶠ p : (ι → ℂ) × Matrix ι ι ℂ in 𝓝 (v, Ω),
      ∀ n, ‖riemannThetaTerm a b p.2 p.1 n‖ ≤ riemannThetaBound a c S n := by sorry
