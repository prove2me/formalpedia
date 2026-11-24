-- Prove2me | Theorems.Thm_GlobalTheory_NormSheaf_IntegralCoeff_isIntegral_normForm
-- name    : GlobalTheory.NormSheaf.IntegralCoeff.isIntegral_normForm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:34.013618+00:00
-- url     : https://prove2.me/theorems/651faa92-0863-4304-a418-cd7e9df56dea
-- title:
--   Integral Coeff: is Integral norm Form
-- statement:
--   The Integral Coeff construction uses the is Integral norm Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L43-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L43-L98

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

theorem GlobalTheory.NormSheaf.IntegralCoeff.isIntegral_normForm (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
    IsIntegral (MvPolynomial (Fin m) A) (GlobalTheory.NormSheaf.normForm K L x) := by sorry
