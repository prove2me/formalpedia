-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_behavioral_value_sign
-- name    : InvIntegration.Behavioral.behavioral_value_sign
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:33.715201+00:00
-- url     : https://prove2.me/theorems/1d829f22-83cc-469b-af18-8caa50cf905b
-- title:
--   p. 13 (PDF 13) (corrected: Π(µ,σ) > 0) — the behavioral value is positive if v∗m > v∗I and negative if v∗m < v∗I
-- statement:
--   Let $\sigma>0$ with $\Pi(\mu,\sigma)>0$ and $\rho\in(-1,1)$, and let $v^*_m$, $v^*_I$ be equilibrium threshold valuations of the multichannel market $N(\mu,\sigma^2)$ and the integrated market $N(2\mu,2(1+\rho)\sigma^2)$. Writing
--   $$\mathrm{BV} = \frac{G(v^*_m)-G(v^*_I)}{\bar G(v^*_m)}\times\frac{\Pi\bigl(2\mu,\sqrt{2(1+\rho)}\,\sigma\bigr)}{2\Pi(\mu,\sigma)}$$
--   for the behavioral value of integration,
--   1. if $v^*_I<v^*_m$ then $\mathrm{BV}>0$;
--   2. if $v^*_m<v^*_I$ then $\mathrm{BV}<0$.
--
--   This reduces the sign of the behavioral value to the comparison of the two threshold valuations.
--
--   **Formalization Note.** The hypothesis $\Pi(\mu,\sigma)>0$ is added: when $\Pi(\mu,\sigma)<0<\Pi(2\mu,\sqrt{2(1+\rho)}\sigma)$ the sign is reversed, so the sentence on the page is false without it.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), p. 13 (PDF 13), first sentence after the derivation of (7) (corrected)

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem behavioral_value_sign (P : Params) (hS : P.Standing) (σ : ℝ) (hσ : 0 < σ)
    (hPi : 0 < Pi P P.μ σ) (ρ : ℝ) (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (qm vm ξm qI vI ξI : ℝ) (hm : IsEquilibrium P P.μ σ qm vm ξm)
    (hI : IsEquilibrium P (2 * P.μ) (sdI σ ρ) qI vI ξI) :
    (vI < vm → 0 < behavioralValue P σ ρ vm vI) ∧
    (vm < vI → behavioralValue P σ ρ vm vI < 0) := by sorry

end InvIntegration.Behavioral
