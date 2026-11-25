-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_exact_hom_one
-- name    : GlobalTheory.FibreAcyclic.exact_hom_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:52.098807+00:00
-- url     : https://prove2.me/theorems/2fc7deac-7103-5668-8621-c092d8192959
-- title:
--   Fibre Acyclic: exact hom one
-- statement:
--   The Fibre Acyclic construction uses the exact hom one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L57-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L57-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemSmulTopOfForallMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory GlobalTheory.FibreAcyclic
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R] [IsLocalRing R]

theorem GlobalTheory.FibreAcyclic.exact_hom_one [IsNoetherianRing R] (N : Ideal R) (hN : N ≤ maximalIdeal R) (M : Type) [AddCommGroup M]
    [Module R M] (hM : ∀ s ∈ N, ∀ x : M, s • x = 0) (g : ℕ) (hE : ∀ j < g, ExtZero (R := R) M j)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : Ideal R, p.IsPrime → N ≤ p → ∃ (K : Type) (_ : Field K) (φ : R →+* K),
      RingHom.ker φ = p ∧ ∀ i, (p ≠ maximalIdeal R ∨ g < i) →
        (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    LinearMap.ker (LinearMap.lcomp R M (C.d 0 1).hom) ≤ LinearMap.range (LinearMap.lcomp R M (C.d 1 2).hom) := by sorry
