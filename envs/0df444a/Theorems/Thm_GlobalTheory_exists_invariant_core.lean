-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_core
-- name    : GlobalTheory.exists_invariant_core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:11.537598+00:00
-- url     : https://prove2.me/theorems/1ba63a3f-0648-4a4a-b853-94af8f84fc30
-- title:
--   Global Theory: exists invariant core
-- statement:
--   The Global Theory construction uses the exists invariant core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L326-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L326-L329

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
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul 𝕜 V] [T2Space V] [FiniteDimensional 𝕜 V]

theorem GlobalTheory.exists_invariant_core (ρ : Representation 𝕜 K V) (hρc : ∀ v, Continuous fun k => ρ k v) :
    ∃ c : InnerProductSpace.Core 𝕜 V, ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v := by sorry
