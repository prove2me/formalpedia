-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_complete_discreteValuationRing_of_mem_closure_cones_alt
-- name    : GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:44.358953+00:00
-- url     : https://prove2.me/theorems/03631b19-bf2c-50a0-b4cf-84757362aaf1
-- title:
--   T: exists complete discrete Valuation Ring of mem closure cones alt
-- statement:
--   The T construction uses the exists complete discrete Valuation Ring of mem closure cones alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCBis.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCBis.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_complete_discreteValuationRing_of_mem_closure_cones_alt : ∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by sorry
