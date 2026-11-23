-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap
-- name    : GrothendieckLB.Supplement.limitingScheme_bound_of_coefficient_gap
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T15:48:28.893283+00:00
-- url     : https://prove2.me/theorems/ae59a9d3-87e7-485f-ab03-f75ad2be0184
-- title:
--   A forward coefficient gap gives a Grothendieck bound for a limiting scheme
-- statement:
--   Let $H$ be the arcsine-normalized correlation of a limiting Krivine scheme and let $b_m$ be its Taylor coefficients at zero. Suppose its nonlinear odd coefficients are absolutely summable, and write
--   $$
--   \Delta_H=\sum_{j\ge0}|b_{2j+3}|.
--   $$
--   If $\gamma>0$ and $\gamma+\Delta_H<b_1$, then
--   $$
--   K_G\le\frac{\pi}{2\gamma}.
--   $$
--   The correlation is odd and holomorphic in the unit disk. Proposition 6.1 gives an inverse branch on a disk of radius greater than $\gamma$ with image in the unit disk and inverse majorant strictly below one at $\gamma$. Locally uniform approximation by ordinary schemes and the strict inverse-majorant transfer pass this certificate to a finite-dimensional scheme, where classical Krivine preprocessing gives the bound.
-- source:
--   Saha, Li, Xue, Chaudhuri, Klivans, Kothari and Meka, New Lower and Upper Bounds for the Grothendieck Constant, https://arxiv.org/pdf/2608.11158v2, Lemma 3.3 (p. 8), Theorem 3.9 and Lemma 3.11 (pp. 11–15), Proposition 6.1 (pp. 19–20), and their combination in the proof of Theorem 6.4 (p. 21).

import Definitions.Def_GrothendieckConstantDefs
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr

namespace GrothendieckLB.Supplement

theorem limitingScheme_bound_of_coefficient_gap {k : ℕ} (S : LimitingScheme k)
    (γ : ℝ) (hγ : 0 < γ)
    (hsum : Summable (fun j : ℕ => |GrothendieckLB.taylorCoeff (2 * j + 3) S.corr|))
    (hgap : γ + (∑' j : ℕ, |GrothendieckLB.taylorCoeff (2 * j + 3) S.corr|) <
        GrothendieckLB.taylorCoeff 1 S.corr) :
    GrothendieckConstant.grothendieckConst ≤ Real.pi / (2 * γ) := by sorry

end GrothendieckLB.Supplement
