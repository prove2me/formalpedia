-- Prove2me | Theorems.Thm_GlobalTheory_NormSheaf_IntegralCoeff_isIntegral_det_of_aeval
-- name    : GlobalTheory.NormSheaf.IntegralCoeff.isIntegral_det_of_aeval
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:06.358373+00:00
-- url     : https://prove2.me/theorems/02178649-c4d9-468b-b9ec-c43dce379c77
-- title:
--   Integral Coeff: is Integral det of aeval
-- statement:
--   The Integral Coeff construction uses the is Integral det of aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CoeffNormFormOfFamilyMemRangeIntegrallyClosed.lean#L27-L34

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

theorem GlobalTheory.NormSheaf.IntegralCoeff.isIntegral_det_of_aeval {R' F : Type} [CommRing R'] [Field F] [Algebra R' F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (g : Polynomial R') (hg : g.Monic)
    (h : Polynomial.aeval M (g.map (algebraMap R' F)) = 0) : IsIntegral R' M.det := by sorry
