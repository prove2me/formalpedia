-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernelFlat_mem_sup_of_exact_fibres
-- name    : GlobalTheory.DualCokernelFlat.mem_sup_of_exact_fibres
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:15.848943+00:00
-- url     : https://prove2.me/theorems/234a39d9-a109-48b4-8258-82a5121ec531
-- title:
--   Dual Cokernel Flat: mem sup of exact fibres
-- statement:
--   The Dual Cokernel Flat construction uses the mem sup of exact fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L66-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/FlatQuotientOfEquivCokerDualMapOfExactFibres.lean#L66-L108

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
open GlobalTheory.DualCokernelFlat

theorem GlobalTheory.DualCokernelFlat.mem_sup_of_exact_fibres {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsRegularLocalRing B] (π : A →+* B) (hs : Surjective π) (g : ℕ) (hg : ringKrullDim B = g)
    (C : CochainComplex (ModuleCat.{0} A) ℕ)
    (hF : ∀ i, Module.Free A (C.X i) ∧ Module.Finite A (C.X i))
    (hn : ∃ n, ∀ i, n < i → IsZero (C.X i))
    (hex : ∀ p : PrimeSpectrum A, RingHom.ker π ≤ p.asIdeal → ∃ (K : Type) (_ : Field K)
      (φ : A →+* K), RingHom.ker φ = p.asIdeal ∧
        ∀ i, (p.asIdeal ≠ IsLocalRing.maximalIdeal A ∨ g < i) →
          (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i)
    (i : ℕ) (x : Module.Dual A (C.X (i + 1)))
    (hx : (C.d i (i + 1)).hom.dualMap x ∈
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X i)))) :
    x ∈ LinearMap.range (C.d (i + 1) (i + 1 + 1)).hom.dualMap ⊔
      (RingHom.ker π • ⊤ : Submodule A (Module.Dual A (C.X (i + 1)))) := by sorry
