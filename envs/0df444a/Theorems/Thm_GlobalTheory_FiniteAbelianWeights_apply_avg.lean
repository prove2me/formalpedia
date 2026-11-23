-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_apply_avg
-- name    : GlobalTheory.FiniteAbelianWeights.apply_avg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:28.9338+00:00
-- url     : https://prove2.me/theorems/0b843416-98c8-4aff-94ee-f9ec9127b7e6
-- title:
--   Finite Abelian Weights: apply avg
-- statement:
--   The Finite Abelian Weights construction uses the apply avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L33-L44

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

theorem GlobalTheory.FiniteAbelianWeights.apply_avg (c : T →* oˣ) (s : T) (x : M) :
    ρ s (avg ρ u c x) = (c s : o) • avg ρ u c x := by sorry
