-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_exists_homotopy
-- name    : GlobalTheory.DualCokernel.exists_homotopy
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:36.542707+00:00
-- url     : https://prove2.me/theorems/68ca426e-e55c-4be0-ad79-2be11f2d52e6
-- title:
--   Dual Cokernel: exists homotopy
-- statement:
--   The Dual Cokernel construction uses the exists homotopy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L234-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L234-L248

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
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)

theorem GlobalTheory.DualCokernel.exists_homotopy (hF : ∀ i, Module.Free R (C.X i) ∧ Module.Finite R (C.X i))
    (n : ℕ) (hn : ∀ i, n < i → IsZero (C.X i)) (p : Ideal R) [hp : p.IsPrime]
    (h : ∀ i, Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField)) (i : ℕ) :
    ∃ (t : R) (_ : t ∉ p) (k₀ : C.X i →ₗ[R] C.X (i - 1)) (k₁ : C.X (i + 1) →ₗ[R] C.X i),
      ∀ x, (C.d (i - 1) i).hom (k₀ x) + k₁ ((C.d i (i + 1)).hom x) = t • x := by sorry
