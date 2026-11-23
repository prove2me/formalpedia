-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_core_of_continuous_coeff
-- name    : GlobalTheory.exists_invariant_core_of_continuous_coeff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:41.224422+00:00
-- url     : https://prove2.me/theorems/caa2e392-b130-4b3b-b355-134c601cb7d8
-- title:
--   Global Theory: exists invariant core of continuous coeff
-- statement:
--   The Global Theory construction uses the exists invariant core of continuous coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L304-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L304-L314

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜]
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem GlobalTheory.exists_invariant_core_of_continuous_coeff {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (ρ : Representation 𝕜 K V)
    (hρc : ∀ (l : Module.Dual 𝕜 V) (v : V), Continuous fun k => l (ρ k v)) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v := by sorry
