-- Prove2me | Theorems.Thm_GlobalTheory_continuous_prod_ofFn_curves
-- name    : GlobalTheory.continuous_prod_ofFn_curves
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:09.152906+00:00
-- url     : https://prove2.me/theorems/598c8242-aaff-46bf-b77a-1a82f612c075
-- title:
--   Global Theory: continuous prod of Fn curves
-- statement:
--   The Global Theory construction uses the continuous prod of Fn curves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SobolevIteratedOneParameterSubgroups.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SobolevIteratedOneParameterSubgroups.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SqIntervalIntegralLeMulIntervalIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.continuous_prod_ofFn_curves {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (hc : ∀ i, Continuous (c i)) :
    Continuous fun t : Fin N → ℝ => (List.ofFn fun i => c i (t i)).prod := by sorry
