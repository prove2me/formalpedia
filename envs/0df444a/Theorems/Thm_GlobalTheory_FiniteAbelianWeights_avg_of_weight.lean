-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight
-- name    : GlobalTheory.FiniteAbelianWeights.avg_of_weight
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:36.014744+00:00
-- url     : https://prove2.me/theorems/8c7dff17-c8b4-47e5-8000-aec7f61cb1a5
-- title:
--   Finite Abelian Weights: avg of weight
-- statement:
--   The Finite Abelian Weights construction uses the avg of weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L46-L49

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

theorem GlobalTheory.FiniteAbelianWeights.avg_of_weight (hu : u * (Fintype.card T : o) = 1) (c : T →* oˣ) (x : M)
    (hx : ∀ t, ρ t x = (c t : o) • x) : avg ρ u c x = x := by sorry
