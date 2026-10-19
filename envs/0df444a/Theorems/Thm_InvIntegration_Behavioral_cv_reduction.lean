-- Prove2me | Theorems.Thm_InvIntegration_Behavioral_cv_reduction
-- name    : InvIntegration.Behavioral.cv_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:23.504767+00:00
-- url     : https://prove2.me/theorems/0041b3b3-d789-42a5-b986-dac6f0013b90
-- title:
--   Proof of Proposition 5, EC pp. 3–5 (PDF 35–37) — the equilibrium depends only on cv; v∗m(σ) = v∗I(2σ/√(2(1 + ρ)))
-- statement:
--   The equilibrium threshold valuation and second-period fill rate depend on the market only through its coefficient of variation:
--   1. If $m,\mathrm{sd},m',\mathrm{sd}'>0$ with $\mathrm{sd}/m = \mathrm{sd}'/m'$, and $(q,v,\xi)$, $(q',v',\xi')$ are equilibria of the markets $N(m,\mathrm{sd}^2)$ and $N(m',\mathrm{sd}'^2)$, then $v=v'$ and $\xi=\xi'$.
--   2. Consequently, for $\sigma>0$ and $\rho\in(-1,1)$,
--   $$v^*_m(\sigma) = v^*_I\Bigl(\frac{2\sigma}{\sqrt{2(1+\rho)}}\Bigr),$$
--   i.e. any equilibrium valuation of the multichannel market $N(\mu,\sigma^2)$ equals any equilibrium valuation of the integrated market with mean $2\mu$ and standard deviation $\sqrt{2(1+\rho)}\cdot 2\sigma/\sqrt{2(1+\rho)}$.
--
--   This reduction is what lets the proof of Proposition 5 compare the two systems through a single function of $cv$.
-- source:
--   Aflaki & Swinney, Inventory Integration with Rational Consumers, SSRN preprint 2842182 (July 2020), EC pp. 3–5 (PDF 35–37), proof of Proposition 5

import Mathlib
import Definitions.Def_InvIntegration_Behavioral_Model

namespace InvIntegration.Behavioral

theorem cv_reduction (P : Params) (hS : P.Standing) :
    (∀ m sd m' sd' : ℝ, 0 < m → 0 < sd → 0 < m' → 0 < sd' → sd / m = sd' / m' →
      ∀ q v ξ q' v' ξ' : ℝ, IsEquilibrium P m sd q v ξ → IsEquilibrium P m' sd' q' v' ξ' →
        v = v' ∧ ξ = ξ') ∧
    (∀ σ : ℝ, 0 < σ → ∀ ρ ∈ Set.Ioo (-1 : ℝ) 1,
      ∀ q v ξ q' v' ξ' : ℝ, IsEquilibrium P P.μ σ q v ξ →
        IsEquilibrium P (2 * P.μ) (sdI (2 * σ / Real.sqrt (2 * (1 + ρ))) ρ) q' v' ξ' → v = v') := by sorry

end InvIntegration.Behavioral
