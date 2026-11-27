-- Prove2me | Theorems.Thm_FracRiccati_Radius_Supplement_prop_C_1
-- name    : FracRiccati.Radius.Supplement.prop_C_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T20:56:19.006921+00:00
-- url     : https://prove2.me/theorems/f61dd922-234b-431f-938c-d6cbfdbd83ee
-- title:
--   Proposition C.1 — closed form for the starting values
-- statement:
--   Let $1/2<\alpha<1$, $\lambda\ne0$, and $\mu,\nu,u\in\mathbb C$. For the case-(a) double coefficients defined by (6.37)–(6.38) with $v=0$, and the real sequence $c_\ell$ defined by (C.63), every integer $\ell\ge1$ satisfies
--   $$a_{2\ell-1,\ell}=\lambda^{\ell-1}\left(\frac{u}{\Gamma(\alpha)}\right)^\ell c_\ell.$$
--   This is the starting-value identity used to establish the exact valuations in Theorem 6.1(a). Both sides vanish appropriately when $u=0$; no nonzero initial-data premise is imposed.
--
--   Differences from the source:
--   - encoding: the proposition occurs inside the proof of case (a) → the order range and lambda nonzero are explicit binders; reason: the range comes from Appendix C.1 and lambda nonzero from the governing Assumption 3.1; nu zero is allowed by Theorem 6.1
--   - encoding: the recurrence for c_l is part of the statement → c_l is computed by startingValues and the same recurrence; reason: the definition is shared and has no assumed identity or unproved theorem
-- source:
--   Callegaro, Grasselli, Pagès, Fast Hybrid Schemes for Fractional Riccati Equations (Rough is not so Tough), arXiv:1805.12587v4, p. 40, Proposition C.1

import Mathlib
import Definitions.Def_FracRiccati_Radius_Supplement_DoubleSeries

namespace FracRiccati.Radius.Supplement

theorem prop_C_1 (α : ℝ) (lam mu nu u : ℂ)
    (hα : 1 / 2 < α) (hα1 : α < 1) (hlam : lam ≠ 0) :
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      doubleCoeff α lam mu nu u 0 (2 * ℓ - 1) ℓ =
        lam ^ (ℓ - 1) * (u / (Real.Gamma α : ℂ)) ^ ℓ * (startingValues α ℓ : ℂ) := by sorry

end FracRiccati.Radius.Supplement
