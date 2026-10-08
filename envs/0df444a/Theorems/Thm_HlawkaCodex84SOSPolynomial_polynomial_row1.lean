-- Prove2me | Theorems.Thm_HlawkaCodex84SOSPolynomial_polynomial_row1
-- name    : HlawkaCodex84SOSPolynomial.polynomial_row1
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T07:43:47.305004+00:00
-- url     : https://prove2.me/theorems/3e7e738f-2c82-4898-a083-886db05b6a45
-- title:
--   Exact polynomial reconstruction of Hlawka cutoff-84 SOS matrix, row 1
-- statement:
--   Let $e\in\mathbb{R}^9$ be an arbitrary perturbation, and let C(e) be the quadratic sum-of-squares matrix and B(e) the radial comparison matrix specified by the exact rational cutoff-84 certificate. For every column $j\in\{0,1,2\}$, row 1 agrees exactly:
--
--   $$C(e)_{1j}=B(e)_{1j}.$$
--
--   This identity holds for all real perturbations, without a box restriction. Together the three row identities identify the stored sum-of-squares expression with the original radial comparison matrix.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant; Codex cutoff84 continuation, Hlawka84_QuadraticSOSBridge.certificateMatrix_eq_comparison, split into three exact rows.

import Definitions.Def_HlawkaCodex84_SOSPolynomialData
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace HlawkaCodex84SOSPolynomial
theorem polynomial_row1 : ∀ (e : Fin 9 → ℝ) (j : Fin 3), HlawkaCodex84SOSPolynomialData.certificateMatrix e 1 j = HlawkaCodex84SOSPolynomialData.comparisonMatrix e 1 j := by sorry
end HlawkaCodex84SOSPolynomial
