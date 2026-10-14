-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_eq60
-- name    : LeveragedPayouts.Unregulated.eq60
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:25.579985+00:00
-- url     : https://prove2.me/theorems/5a66557d-9440-460e-ad98-01f34a4579c1
-- title:
--   (60), Appendix B, proof of Proposition 11, p. 56 — the date-0 surplus has a positive derivative at the rate r̂ where l(r̂) = l_ρ
-- statement:
--   In the economy of the mission, let $\rho\in(0,1)$ and let $l_\rho$ be the first-best date-0 labour. Let $0<a<b\le R$ and let $L:(a,b)\to(0,1]$ be a labour response, i.e. $L(r)$ is the labour demand at $r$ for every $r\in(a,b)$. Let $\hat r\in(a,b)$ with $L(\hat r)=l_\rho$, and suppose $L$ is differentiable at $\hat r$ with derivative $L'(\hat r)$. Write $e(r)=\pi R/(2R-r)$ and $e'(\hat r)=\pi R/(2R-\hat r)^2$. Then $r\mapsto\Sigma_\rho(e(r),L(r))$ is differentiable at $\hat r$ with derivative
--   $$\Sigma_\rho'(\hat r)=e'(\hat r)\Big(1-\frac{e(\hat r)}{\pi}\Big)\frac{f(L(\hat r))}{R}+L'(\hat r)\Big[\Big(e(\hat r)-\frac{e(\hat r)^2}{2\pi}\Big)\frac{f'(L(\hat r))}{R}-\rho g'(1-L(\hat r))\Big],$$
--   and this derivative is strictly positive.
--
--   This is (60): at the rate where the unregulated labour demand equals its first-best level, raising the rate still increases date-0 surplus, because the gain in effort outweighs the loss in employment. It is the key step of Proposition 11.
--
--   **Formalization Note** The paper calls $l(r)$ "obviously differentiable"; here differentiability of the labour response at $\hat r$ is a hypothesis.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 56, Appendix B, proof of Proposition 11, (59)–(60)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated
theorem eq60 (E : Economy) (ρ lρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlρ : IsFirstBestLabor E ρ lρ) (L : ℝ → ℝ) (a b rhat : ℝ) (ha : 0 < a) (hb : b ≤ E.R)
    (hrhat : rhat ∈ Set.Ioo a b) (hL : ∀ r ∈ Set.Ioo a b, IsLaborDemand E r (L r))
    (hLrhat : L rhat = lρ) (L' : ℝ) (hL' : HasDerivAt L L' rhat) :
    HasDerivAt (fun r => surplus E ρ (effort E r) (L r))
      (E.π * E.R / (2 * E.R - rhat) ^ 2 * (1 - effort E rhat / E.π) * E.f (L rhat) / E.R +
        L' * ((effort E rhat - effort E rhat ^ 2 / (2 * E.π)) * deriv E.f (L rhat) / E.R -
          ρ * deriv E.g (1 - L rhat))) rhat ∧
    0 < E.π * E.R / (2 * E.R - rhat) ^ 2 * (1 - effort E rhat / E.π) * E.f (L rhat) / E.R +
        L' * ((effort E rhat - effort E rhat ^ 2 / (2 * E.π)) * deriv E.f (L rhat) / E.R -
          ρ * deriv E.g (1 - L rhat)) := by sorry
end LeveragedPayouts.Unregulated
