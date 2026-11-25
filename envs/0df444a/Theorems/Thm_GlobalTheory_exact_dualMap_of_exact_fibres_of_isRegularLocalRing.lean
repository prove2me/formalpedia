-- Prove2me | Theorems.Thm_GlobalTheory_exact_dualMap_of_exact_fibres_of_isRegularLocalRing
-- name    : GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:25.300889+00:00
-- url     : https://prove2.me/theorems/c916e54a-4f89-4440-8990-94a5fe33010a
-- title:
--   Global Theory: exact dual Map of exact fibres of is Regular Local Ring
-- statement:
--   The Global Theory construction uses the exact dual Map of exact fibres of is Regular Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRing.lean#L28-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExactDualMapOfExactFibresOfIsRegularLocalRing.lean#L28-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open DualCokernel

theorem GlobalTheory.exact_dualMap_of_exact_fibres_of_isRegularLocalRing :
    ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (g : ℕ), ringKrullDim A = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ i, Function.Exact (C.d (i + 1) (i + 2)).hom.dualMap (C.d i (i + 1)).hom.dualMap := by sorry
