-- Prove2me | Theorems.Thm_GlobalTheory_FibreAcyclic_injective_of_exact
-- name    : GlobalTheory.FibreAcyclic.injective_of_exact
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:18.991673+00:00
-- url     : https://prove2.me/theorems/d97689e2-d85c-4551-aac7-a52dec623a87
-- title:
--   Fibre Acyclic: injective of exact
-- statement:
--   The Fibre Acyclic construction uses the injective of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L144-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemSmulTopOfForallMem.lean#L144-L203

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
omit [IsLocalRing R]

theorem GlobalTheory.FibreAcyclic.injective_of_exact {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra A R] [Module.Flat A R]
    {F₀ F₁ F₂ : Type} [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup F₂] [Module R F₂]
    [Module.Free R F₀] [Module.Finite R F₀] [Module.Free R F₁] [Module.Finite R F₁] [Module.Free R F₂]
    (a : F₀ →ₗ[R] F₁) (b : F₁ →ₗ[R] F₂) (hab : ∀ x, b (a x) = 0)
    (hex : LinearMap.ker (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) a) ≤
      LinearMap.range (LinearMap.lcomp R (R ⧸ (maximalIdeal A).map (algebraMap A R)) b))
    (I : Ideal R) (hI : I ≠ ⊤) (e : (Module.Dual R F₀ ⧸ LinearMap.range a.dualMap) ≃ₗ[R] R ⧸ I)
    (hs : Surjective (algebraMap A (R ⧸ I))) : Injective (algebraMap A (R ⧸ I)) := by sorry
