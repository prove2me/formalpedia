-- Prove2me | Theorems.Thm_LeveragedPayouts_ShockSize_eq65
-- name    : LeveragedPayouts.ShockSize.eq65
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:27:57.820825+00:00
-- url     : https://prove2.me/theorems/bf209f31-5e73-4375-a388-6bf1df7c5114
-- title:
--   (65), p. 57 — the factorization $\Sigma_\rho'(r)=(R-r)[A+\frac{4w^*}{\pi Rf''(l(r))}B]$
-- statement:
--   Fix an economy, a real number $\rho$, and an open interval $(a,b)$ of rates with $0<a<b\le R$. Let $l(\cdot)$ be the date-0 labour demand on $(a,b)$, as in (63), and let
--   $$\Sigma_\rho(r)=\Big(e(r)-\frac{e(r)^2}{2\pi}\Big)\frac{f(l(r))}{R}+\rho\,g(1-l(r)),\qquad e(r)=\frac{\pi R}{2R-r}.$$
--   Then $\Sigma_\rho$ is differentiable at every $r\in(a,b)$, with
--   $$\Sigma_\rho'(r)=(R-r)\left[\underbrace{\frac{\pi f(l(r))}{(2R-r)^3}}_{A}+\frac{4w^*}{\pi R f''(l(r))}\underbrace{\left[\frac{\pi(3R-2r)f'(l(r))}{2(2R-r)^2}-\rho\,g'(1-l(r))\right]}_{B}\right]. \tag{65}$$
--
--   Term $A$ is the effect of the rate on productive efficiency, term $B$ the effect through scale. The factor $R-r$ is what makes the local analysis near $r=R$ in Step 1 work.
--
--   **Formalization Note** The surplus is `surplus E ρ (effort E s) (L s)`; on $(a,b)$, $\min\{s,R\}=s$. The derivatives $f',f'',g'$ are `deriv`, evaluated at $l(r)\in(0,1)$ and $1-l(r)>0$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 57, Appendix B, proof of Proposition 12, Step 1, (65)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.ShockSize

theorem eq65 (E : LeveragedPayouts.Unregulated.Economy) (L : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hbR : b ≤ E.R)
    (hL : ∀ r ∈ Set.Ioo a b, LeveragedPayouts.Unregulated.IsLaborDemand E r (L r)) (ρ : ℝ) :
    ∀ r ∈ Set.Ioo a b,
      HasDerivAt (fun s => LeveragedPayouts.Unregulated.surplus E ρ (LeveragedPayouts.Unregulated.effort E s) (L s))
        ((E.R - r) * (E.π * E.f (L r) / (2 * E.R - r) ^ 3 +
          4 * E.wstar / (E.π * E.R * deriv (deriv E.f) (L r)) *
            (E.π * (3 * E.R - 2 * r) * deriv E.f (L r) / (2 * (2 * E.R - r) ^ 2) -
              ρ * deriv E.g (1 - L r)))) r := by sorry

end LeveragedPayouts.ShockSize
