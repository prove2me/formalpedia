-- Prove2me | Theorems.Thm_HlawkaCodex84SOSPolynomial_polynomial_row0
-- name    : HlawkaCodex84SOSPolynomial.polynomial_row0
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T07:42:49.632202+00:00
-- url     : https://prove2.me/theorems/469bec50-d248-4e8a-96e8-1d43ba489404
-- title:
--   Exact polynomial reconstruction of Hlawka cutoff-84 SOS matrix, row 0
-- statement:
--   Let $e\in\mathbb{R}^9$ be an arbitrary perturbation, and let C(e) be the quadratic sum-of-squares matrix and B(e) the radial comparison matrix specified by the exact rational cutoff-84 certificate. For every column $j\in\{0,1,2\}$, row 0 agrees exactly:
--
--   $$C(e)_{0j}=B(e)_{0j}.$$
--
--   This identity holds for all real perturbations, without a box restriction. Together the three row identities identify the stored sum-of-squares expression with the original radial comparison matrix.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant; Codex cutoff84 continuation, Hlawka84_QuadraticSOSBridge.certificateMatrix_eq_comparison, split into three exact rows.

import Definitions.Def_HlawkaCodex84_SOSPolynomialData
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace HlawkaCodex84SOSPolynomial
theorem polynomial_row0 : ∀ (e : Fin 9 → ℝ) (j : Fin 3), HlawkaCodex84SOSPolynomialData.certificateMatrix e 0 j = HlawkaCodex84SOSPolynomialData.comparisonMatrix e 0 j := by sorry
end HlawkaCodex84SOSPolynomial
