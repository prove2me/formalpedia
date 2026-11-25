-- Prove2me | Theorems.Thm_GlobalTheory_T_exact_dualMap_of_exactAt_extendScalars_fibres
-- name    : GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:14.643548+00:00
-- url     : https://prove2.me/theorems/d58454ed-c192-59e0-aa96-c4639a182042
-- title:
--   T: exact dual Map of exact At extend Scalars fibres
-- statement:
--   The T construction uses the exact dual Map of exact At extend Scalars fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRingStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRingStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exact_dualMap_of_exactAt_extendScalars_fibres : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ, (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) → (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) → (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) → ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by sorry
