-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_mem_weightSpace_iff
-- name    : GlobalTheory.FiniteAbelianWeights.mem_weightSpace_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:09.704581+00:00
-- url     : https://prove2.me/theorems/b63fa0dc-a036-4c81-ae9b-325b2349430d
-- title:
--   Finite Abelian Weights: mem weight Space iff
-- statement:
--   The Finite Abelian Weights construction uses the mem weight Space iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L14-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open GlobalTheory.FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]

theorem GlobalTheory.FiniteAbelianWeights.mem_weightSpace_iff {ι : Type} (f : ι → M →ₗ[o] M) (a : ι → o) (x : M) :
    x ∈ (⨅ t, LinearMap.ker (f t - a t • LinearMap.id)) ↔ ∀ t, f t x = a t • x := by sorry
