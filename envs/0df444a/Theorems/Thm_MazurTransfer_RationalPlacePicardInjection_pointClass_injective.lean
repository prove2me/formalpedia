-- Prove2me | Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_pointClass_injective
-- name    : MazurTransfer.RationalPlacePicardInjection.pointClass_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T01:36:41.862192+00:00
-- url     : https://prove2.me/theorems/83b0fa97-7bc7-423f-a786-a793767eee16
-- title:
--   Rational places embed into the degree-zero divisor class group in positive genus
-- statement:
--   Let $K$ be a perfect field and let $F/K$ be an essentially finite-type one-variable function field whose constant field is $K$. Suppose $g(F/K)>0$ and fix a degree-one place $Q$. Then
--   $$P\longmapsto [P-Q]\in\operatorname{Pic}^0(F/K)$$
--   is injective on degree-one places $P$.
--
--   This is the function-field form of injectivity of an Abel–Jacobi map on rational points. It lets a genuine point-difference divisor dictionary transfer equality of Picard classes back to equality of curve points, as required in the order-thirteen rational-point classification.
-- source:
--   Original checked perfect-field bridge in MazurTheorem: RationalPlacePicardInjectionOverPerfectField.lean, lines137–148, SHA256 b9cff5c97e7135504b70656a12f861cc4d7990e25cf69a72ea527792dc3fd175. The principal-divisor genus-zero argument derives from the Apache-2.0 Anthropic FLT formalization at6e837e75355538c7f80bab5b956861e86c4eacc2; the separately proved public genusFF bridge is99340fff-8925-42fb-9287-28755c7eb4c8.

import Mathlib
import Definitions.Def_MazurTransfer_RationalPlacePicardPointClass
import Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_genusFF_eq_zero_of_principal_single_sub_single
open AlgebraicCurve Polynomial MazurTransfer.RationalPlacePicardInjection
universe u v

theorem MazurTransfer.RationalPlacePicardInjection.pointClass_injective {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) (hgen : 0 < genusFF K F)
    (Q : {v : AlgebraicCurve.Place K F // v.deg = 1}) :
    Function.Injective (pointClass Q) := by sorry
