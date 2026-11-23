-- Prove2me | Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_of_weight_ne
-- name    : GlobalTheory.FiniteAbelianWeights.avg_of_weight_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:47.291791+00:00
-- url     : https://prove2.me/theorems/25c465e3-2c38-4beb-a9c4-37dca2bc9f80
-- title:
--   Finite Abelian Weights: avg of weight ne
-- statement:
--   The Finite Abelian Weights construction uses the avg of weight ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/FiniteAbelianWeightDecomposition.lean#L51-L65

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

theorem GlobalTheory.FiniteAbelianWeights.avg_of_weight_ne [IsDomain o] (c d : T →* oˣ) (hcd : d ≠ c) (x : M)
    (hx : ∀ t, ρ t x = (d t : o) • x) : avg ρ u c x = 0 := by sorry
