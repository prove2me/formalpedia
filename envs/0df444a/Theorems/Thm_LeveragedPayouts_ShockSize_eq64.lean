-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_eq64
-- name    : LeveragedPayouts.ShockSize.eq64
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:27:56.45962+00:00
-- url     : https://prove2.me/theorems/480a6567-0c0f-402e-9e72-245461e1070a
-- title:
--   (64), p. 57 — the labour response is differentiable with $l'(r)=4w^*(R-r)/(\pi R f''(l(r)))$
-- statement:
--   Fix an economy and an open interval $(a,b)$ of rates with $0<a<b\le R$. Let $l(\cdot)$ be a function such that, for every $r\in(a,b)$, $l(r)$ is the date-0 labour demand at $r$:
--   $$\frac{\pi R f'(l(r))}{2(2R-r)}=r\,w^*,\qquad 0<l(r)\le 1. \tag{63}$$
--   Then $l$ is differentiable at every $r\in(a,b)$, with
--   $$l'(r)=\frac{4w^*(R-r)}{\pi R f''(l(r))}. \tag{64}$$
--
--   This is the derivative of the labour response used in the factorization (65) of the marginal surplus.
--
--   **Formalization Note** The paper writes "for $r\in(0,1)$", a printed slip for the rates below $R$ at which $l(r)<1$; the interval $(a,b)$ with $b\le R$ encodes it. Differentiability of $l$ is part of the conclusion, not a hypothesis. $f''$ is `deriv (deriv E.f)`, evaluated at $l(r)>0$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 57, Appendix B, proof of Proposition 12, Step 1, (63)–(64)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem eq64 (E : LeveragedPayouts.Unregulated.Economy) (L : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hbR : b ≤ E.R)
    (hL : ∀ r ∈ Set.Ioo a b, LeveragedPayouts.Unregulated.IsLaborDemand E r (L r)) :
    ∀ r ∈ Set.Ioo a b,
      HasDerivAt L (4 * E.wstar * (E.R - r) / (E.π * E.R * deriv (deriv E.f) (L r))) r := by sorry

end LeveragedPayouts.ShockSize
