-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_eq_A6_corrected
-- name    : NegAdPosition.CoLocate.eq_A6_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:28.954979+00:00
-- url     : https://prove2.me/theorems/413ccac1-8e27-439c-9503-b701cbf6b9d0
-- title:
--   (A6′), p. A6 (PDF 49), corrected — closed form of the entrant's expected demand from locating apart
-- statement:
--   Consider the strategies of the proof of Proposition 2 with Bayes beliefs. Assume the standing assumptions, Assumption 1′, (A1a), (A1c) and $\delta < \Pi + \sigma_\beta\beta$. Then the entrant's expected demand from locating apart, over the independent prior, is
--   $$E[D_2 \mid x_2 = R] = \frac{1}{\bar\gamma - \underline\gamma}\Big[\bar\gamma + \sigma_\beta(1-\sigma_\beta)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\sigma_\beta)^2\Pi - (1-\sigma_\beta)\big(\sigma_\beta + (1-\sigma_\beta)\sigma_\Pi(1-\sigma_\Pi)\big)\delta\Big].$$
--
--   Together with (A5′) this gives the entrant's location trade-off in closed form.
--
--   **Formalization Note.** The paper prints the $\Pi$-coefficient $(1-\sigma_\Pi)\sigma_\Pi(1-\sigma_\beta)(1-3\sigma_\beta)$; the correct coefficient is $(1-\sigma_\Pi)\sigma_\Pi(1-\sigma_\beta)^2$. The difference, $2\sigma_\Pi(1-\sigma_\Pi)\sigma_\beta(1-\sigma_\beta)\Pi/(\bar\gamma-\underline\gamma)$, comes from Table A5's row $\{0, \cdot, -\beta, 0\}$, which contradicts the weak-opponent clause of the strategies: with $P_2 = \Pi$, the entrant faces a weak opponent, advertises positively, and takes both locations. Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. A6 (PDF 49), (A6), corrected; Table A5

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem eq_A6_corrected (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a)
    (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) :
    expEntrantDemand P copnAd (bayes P copnAd) .R =
      (P.γhi + P.σB * (1 - P.σB) * P.β + (1 - P.σP) * P.σP * (1 - P.σB) ^ 2 * P.Pi
          - (1 - P.σB) * (P.σB + (1 - P.σB) * P.σP * (1 - P.σP)) * P.δ) / (P.γhi - P.γlo) := by sorry

end NegAdPosition.CoLocate
