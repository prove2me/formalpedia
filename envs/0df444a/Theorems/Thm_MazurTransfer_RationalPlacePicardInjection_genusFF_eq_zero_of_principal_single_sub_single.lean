-- Prove2me | Theorems.Thm_MazurTransfer_RationalPlacePicardInjection_genusFF_eq_zero_of_principal_single_sub_single
-- name    : MazurTransfer.RationalPlacePicardInjection.genusFF_eq_zero_of_principal_single_sub_single
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T01:24:54.612756+00:00
-- url     : https://prove2.me/theorems/99340fff-8925-42fb-9287-28755c7eb4c8
-- title:
--   A principal difference of distinct places, one rational, forces genus zero
-- statement:
--   Let $K$ be a perfect field and let $F/K$ be an essentially finite-type one-variable function field whose constant field is $K$. Let $P$ and $Q$ be distinct places of $F/K$, and assume that $Q$ has degree one. If the divisor $P-Q$ is principal, then
--   $$g(F/K)=0.$$
--   Here $g(F/K)$ is the function-field genus defined by the Riemann–Roch theory. The constant-field assumption is explicit; no rationality hypothesis on $P$ is added.
--
--   Taking the contrapositive shows that the classes of degree-one places in the degree-zero divisor class group distinguish points on every positive-genus curve. This is the geometric injectivity step used in the order-thirteen Abel–Jacobi argument.
-- source:
--   Weil-canonical genusFF adaptation by Vas and contributors, RationalPlacePicardInjectionOverPerfectField.lean, lines 55–129, SHA256 b9cff5c97e7135504b70656a12f861cc4d7990e25cf69a72ea527792dc3fd175. The original pole/independent-powers argument and attribution are retained from the Apache-2.0 Anthropic FLT formalization at exact commit 6e837e75355538c7f80bab5b956861e86c4eacc2: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_AlgebraicCurve_genus_eq_zero_of_isPrincipal_single_sub_single.lean . This statement uses the checked Weil-canonical Riemann–Roch formula for genusFF instead of assuming a canonical-differential genus comparison.

import Mathlib
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
open AlgebraicCurve Polynomial
universe u v

theorem MazurTransfer.RationalPlacePicardInjection.genusFF_eq_zero_of_principal_single_sub_single {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F]
    [Algebra K F] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F)
    {P Q : AlgebraicCurve.Place K F} (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genusFF K F = 0 := by sorry
