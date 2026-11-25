-- Prove2me | Theorems.Thm_GlobalTheory_flat_quotient_of_equiv_coker_dualMap_of_exact_fibres
-- name    : GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:35.895096+00:00
-- url     : https://prove2.me/theorems/41c3e86a-15a6-41da-ac1b-dd0bce66665d
-- title:
--   Global Theory: flat quotient of equiv coker dual Map of exact fibres
-- statement:
--   The Global Theory construction uses the flat quotient of equiv coker dual Map of exact fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L114-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L114-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatCokerOfComplexExactModMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FlatQuotientOfEquivCokerDualMapOfExactFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits TensorProduct Function
open GlobalTheory
open DualCokernelFlat

theorem GlobalTheory.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres :
    ∀ (V A : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] [CommRing A]
      [IsNoetherianRing A] [IsLocalRing A] [Algebra V A] [IsLocalHom (algebraMap V A)]
      [Module.Flat V A] (g : ℕ),
      IsRegularLocalRing (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) →
      ringKrullDim (A ⧸ ((IsLocalRing.maximalIdeal V).map (algebraMap V A))) = g →
      ∀ C : CochainComplex (ModuleCat.{0} A) ℕ,
      (∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i)) → (∃ n, ∀ i, n < i → IsZero (C.X i)) →
      (∀ p : PrimeSpectrum A, ((IsLocalRing.maximalIdeal V).map (algebraMap V A)) ≤ p.asIdeal →
        ∃ (K : Type) (_ : Field K) (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
          ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
            (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) →
      ∀ I : Ideal A, Nonempty ((Module.Dual A (C.X 0) ⧸
        LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[A] (A ⧸ I)) → Module.Flat V (A ⧸ I) := by sorry
