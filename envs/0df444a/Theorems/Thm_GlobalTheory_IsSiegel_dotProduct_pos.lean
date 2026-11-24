-- Prove2me | Theorems.Thm_GlobalTheory_IsSiegel_dotProduct_pos
-- name    : GlobalTheory.IsSiegel.dotProduct_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:53:02.812205+00:00
-- url     : https://prove2.me/theorems/3353b63c-3105-47db-9a1b-2fe22b9f5d28
-- title:
--   Is Siegel: dot Product pos
-- statement:
--   The Is Siegel construction uses the dot Product pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/ExistsEventuallyNormRiemannThetaTermLe.lean#L49-L51

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

theorem GlobalTheory.IsSiegel.dotProduct_pos [Fintype ι] {Ω : Matrix ι ι ℂ} (h : IsSiegel Ω) {x : ι → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Ω.map Complex.im *ᵥ x) := by sorry
