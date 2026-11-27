-- Prove2me | Theorems.Thm_GlobalTheory_isSMulRegular_coker_dualMap_of_exact_fibres
-- name    : GlobalTheory.isSMulRegular_coker_dualMap_of_exact_fibres
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:48.206062+00:00
-- url     : https://prove2.me/theorems/27a27d27-3942-53ee-a454-df8da9309bd2
-- title:
--   Global Theory: is SMul Regular coker dual Map of exact fibres
-- statement:
--   The Global Theory construction uses the is SMul Regular coker dual Map of exact fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L256-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L256-L330

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
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

theorem GlobalTheory.isSMulRegular_coker_dualMap_of_exact_fibres :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (ϖ : A) (g : ℕ),
      ϖ ∈ nonZeroDivisors A → IsRegularLocalRing (A ⧸ Ideal.span {ϖ}) →
      ringKrullDim (A ⧸ Ideal.span {ϖ}) = g → ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ϖ ∈ p.asIdeal → ∃ (K : Type) (_ : Field K) (φ : A →+* K),
        RingHom.ker φ = p.asIdeal ∧ ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      IsSMulRegular (Module.Dual A (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ϖ := by sorry
