-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_eq_A5_corrected
-- name    : NegAdPosition.CoLocate.eq_A5_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:32.92116+00:00
-- url     : https://prove2.me/theorems/0ef6f2b3-2494-4d22-8d7a-abd96ebc4d04
-- title:
--   (A5′), p. A6 (PDF 49), corrected — closed form of the entrant's expected demand from co-locating
-- statement:
--   Consider the strategies of the proof of Proposition 2 with Bayes beliefs. Assume the standing assumptions, Assumption 1′, (A1a) $\beta > (1-\sigma_\Pi)\Pi + \delta$, (A1c) $\Pi > (1-\rho)(1-\sigma_\beta)\beta$ and $\delta < \Pi + \sigma_\beta\beta$. Then the entrant's expected demand from co-locating, over the correlated prior, is
--   $$E[D_2 \mid x_2 = L] = \frac{1}{\bar\gamma - \underline\gamma}\Big[\bar\gamma + \sigma_\beta(1-\sigma_\beta)(1-\sigma_\Pi)(1-\rho)(1-\sigma_\Pi+\rho\sigma_\Pi)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\rho)\Pi - \frac{\delta}{2}\Big].$$
--
--   Together with (A6′) this gives the entrant's location trade-off in closed form.
--
--   **Formalization Note.** The paper prints the factor $(1-\rho+\rho\sigma_\Pi)$ where the sum of its own Table A4 gives $(1-\sigma_\Pi+\rho\sigma_\Pi)$; the printed (A5) is off by $\sigma_\beta(1-\sigma_\beta)(1-\sigma_\Pi)(1-\rho)(\rho-\sigma_\Pi)\beta/(\bar\gamma-\underline\gamma)$. The hypotheses (A1a), (A1c) and $\delta < \Pi + \sigma_\beta\beta$ make the strategies' prescriptions the ones Lemmas 1–4 select, which is what the paper's "the outcomes of the advertising sub-games as given in Lemmas 1–4" means. Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. A6 (PDF 49), (A5), corrected; Table A4

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem eq_A5_corrected (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a)
    (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) :
    expEntrantDemand P copnAd (bayes P copnAd) .L =
      (P.γhi + P.σB * (1 - P.σB) * (1 - P.σP) * (1 - P.ρ) * (1 - P.σP + P.ρ * P.σP) * P.β
          + (1 - P.σP) * P.σP * (1 - P.ρ) * P.Pi - P.δ / 2) / (P.γhi - P.γlo) := by sorry

end NegAdPosition.CoLocate
