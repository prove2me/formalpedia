-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_exists_eventually_mul_dotProduct_le
-- name    : GlobalTheory.IsSiegel.exists_eventually_mul_dotProduct_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:26.032044+00:00
-- url     : https://prove2.me/theorems/1dc5b859-f908-469d-b3a9-b4f61764728a
-- title:
--   Is Siegel: exists eventually mul dot Product le
-- statement:
--   The Is Siegel construction uses the exists eventually mul dot Product le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L173-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L173-L204

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

theorem GlobalTheory.IsSiegel.exists_eventually_mul_dotProduct_le {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) :
    ∃ c > 0, ∀ᶠ Ω' in 𝓝 Ω, ∀ x : ι → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Matrix.map Ω' Complex.im *ᵥ x) := by sorry
