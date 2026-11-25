-- Prove2me | Theorems.Thm_GlobalTheory_DualCokernel_exact_fibre
-- name    : GlobalTheory.DualCokernel.exact_fibre
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:06:41.279484+00:00
-- url     : https://prove2.me/theorems/bda2ab4b-6db9-43df-a352-6a460cf7dc56
-- title:
--   Dual Cokernel: exact fibre
-- statement:
--   The Dual Cokernel construction uses the exact fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L223-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsSMulRegularCokerDualMapOfExactFibres.lean#L223-L232

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

theorem GlobalTheory.DualCokernel.exact_fibre (p : Ideal R) [p.IsPrime] {K : Type} [Field K] (φ : R →+* K)
    (hφ : RingHom.ker φ = p) (i : ℕ)
    (h : (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField) := by sorry
