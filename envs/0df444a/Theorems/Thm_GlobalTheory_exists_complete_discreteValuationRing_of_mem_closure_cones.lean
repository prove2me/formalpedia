-- Prove2me | Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_of_mem_closure_cones
-- name    : GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:30:43.08681+00:00
-- url     : https://prove2.me/theorems/23899653-7cd0-4c92-ab05-12a956072ecc
-- title:
--   Global Theory: exists complete discrete Valuation Ring of mem closure cones
-- statement:
--   The Global Theory construction uses the exists complete discrete Valuation Ring of mem closure cones property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L65-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L65-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_complete_discreteValuationRing_of_mem_closure_cones :
    ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by sorry
