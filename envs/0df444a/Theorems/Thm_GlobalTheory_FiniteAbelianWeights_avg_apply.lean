-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_apply
-- name    : GlobalTheory.FiniteAbelianWeights.avg_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:27.384847+00:00
-- url     : https://prove2.me/theorems/9cc568f8-1b18-4871-ba01-c0ca99db67b8
-- title:
--   Finite Abelian Weights: avg apply
-- statement:
--   The Finite Abelian Weights construction uses the avg apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L23-L25

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
variable [Fintype T] (ρ : Representation o T M) (u : o)

theorem GlobalTheory.FiniteAbelianWeights.avg_apply (c : T →* oˣ) (x : M) :
    avg ρ u c x = u • ∑ t : T, (((c t)⁻¹ : oˣ) : o) • ρ t x := by sorry
