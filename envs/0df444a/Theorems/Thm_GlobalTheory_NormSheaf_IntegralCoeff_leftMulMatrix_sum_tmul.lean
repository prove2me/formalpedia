-- Prove2me | Theorems.Thm_GlobalTheory_NormSheaf_IntegralCoeff_leftMulMatrix_sum_tmul
-- name    : GlobalTheory.NormSheaf.IntegralCoeff.leftMulMatrix_sum_tmul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:41:53.385487+00:00
-- url     : https://prove2.me/theorems/4e912e00-b057-46b6-abc8-e8e1b8ee15d6
-- title:
--   Integral Coeff: left Mul Matrix sum tmul
-- statement:
--   The Integral Coeff construction uses the left Mul Matrix sum tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L15-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
noncomputable section
open GlobalTheory GlobalTheory.NormSheaf GlobalTheory.NormSheaf.IntegralCoeff
open MvPolynomial
open scoped TensorProduct

theorem GlobalTheory.NormSheaf.IntegralCoeff.leftMulMatrix_sum_tmul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (x : Fin m → L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis (MvPolynomial (Fin m) K) (Module.finBasis K L))
      (∑ i, (X i : MvPolynomial (Fin m) K) ⊗ₜ[K] x i) =
    ∑ i, (X i : MvPolynomial (Fin m) K) •
      (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K) := by sorry
