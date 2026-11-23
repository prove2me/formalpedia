-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_sum_avg
-- name    : GlobalTheory.FiniteAbelianWeights.sum_avg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:33.735806+00:00
-- url     : https://prove2.me/theorems/da074428-bcba-43ce-b496-5ec370374a4e
-- title:
--   Finite Abelian Weights: sum avg
-- statement:
--   The Finite Abelian Weights construction uses the sum avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L67-L75

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

theorem GlobalTheory.FiniteAbelianWeights.sum_avg [IsDomain o] [HasEnoughRootsOfUnity o (Monoid.exponent T)] [Fintype (T →* oˣ)]
    (hu : u * (Fintype.card T : o) = 1) (x : M) : ∑ c : T →* oˣ, avg ρ u c x = x := by sorry
