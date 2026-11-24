-- Prove2me | Theorems.Thm_GlobalTheory_discreteTopology_span_of_linearIndependent
-- name    : GlobalTheory.discreteTopology_span_of_linearIndependent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:06.366809+00:00
-- url     : https://prove2.me/theorems/e20d30cd-f304-4d73-b5ca-b7113997b903
-- title:
--   Global Theory: discrete Topology span of linear Independent
-- statement:
--   The Global Theory construction uses the discrete Topology span of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L118-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/DiscreteTopologySpanOfLinearIndependent.lean#L118-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DiscreteTopologySpanOfLinearIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Module Submodule Matrix
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

theorem GlobalTheory.discreteTopology_span_of_linearIndependent {ι : Type*} {v : ι → V}
    (hv : LinearIndependent ℝ v) : DiscreteTopology (span ℤ (Set.range v)) := by sorry
