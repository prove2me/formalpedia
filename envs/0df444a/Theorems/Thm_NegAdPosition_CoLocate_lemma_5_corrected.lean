-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_lemma_5_corrected
-- name    : NegAdPosition.CoLocate.lemma_5_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:23.570583+00:00
-- url     : https://prove2.me/theorems/a7de5672-89c7-4dae-81c2-3c62769a546e
-- title:
--   Lemma 5′, p. 23, corrected — given the sub-game outcomes of Lemmas 1–4, the entrant co-locates iff (A1d′)
-- statement:
--   Consider the strategies of the proof of Proposition 2 with Bayes beliefs, and assume the standing assumptions, Assumption 1′, (A1a), (A1c) and $\delta < \Pi + \sigma_\beta\beta$, so that the advertising sub-games are played as in Lemmas 1–4. Then the entrant weakly prefers co-location, $E[D_2 \mid x_2 = R] \le E[D_2 \mid x_2 = L]$, if and only if
--   $$\sigma_\beta(1-\sigma_\beta)(1-\sigma_\Pi)(1-\rho)(1-\sigma_\Pi+\rho\sigma_\Pi)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\rho)\Pi - \frac{\delta}{2} \ \ge\ \sigma_\beta(1-\sigma_\beta)\beta + (1-\sigma_\Pi)\sigma_\Pi(1-\sigma_\beta)^2\Pi - (1-\sigma_\beta)\big(\sigma_\beta + (1-\sigma_\beta)\sigma_\Pi(1-\sigma_\Pi)\big)\delta. \tag{A1d′}$$
--   In the layout of the paper's Lemma 5 this reads
--   $$(1-\sigma_\Pi)\sigma_\Pi\big((1-\rho) - (1-\sigma_\beta)^2\big)\Pi \ \ge\ \sigma_\beta(1-\sigma_\beta)\big(1 - (1-\sigma_\Pi)(1-\rho)(1-\sigma_\Pi+\rho\sigma_\Pi)\big)\beta + \big(0.5 - (1-\sigma_\beta)(\sigma_\beta + (1-\sigma_\beta)\sigma_\Pi(1-\sigma_\Pi))\big)\delta.$$
--
--   This is the entrant's positioning trade-off: serving a differentiated product against the risk of a negative advertising attack when located apart.
--
--   **Formalization Note.** The printed Lemma 5 has $(1-\sigma_\beta)(1-3\sigma_\beta)$ in place of $(1-\sigma_\beta)^2$ and $(1-\rho+\rho\sigma_\Pi)$ in place of $(1-\sigma_\Pi+\rho\sigma_\Pi)$, inherited from the slips in (A5) and (A6); with the printed condition the equivalence is false (see the mission description). Assumption 1′ uses $\underline\gamma < -\Pi$.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 23 (PDF 23), Lemma 5, corrected; (A1d), p. A4 (PDF 47), corrected

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem lemma_5_corrected (P : Params) (hS : P.Standing) (hA1 : P.Assumption1) (ha : P.A1a)
    (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) :
    expEntrantDemand P copnAd (bayes P copnAd) .R ≤ expEntrantDemand P copnAd (bayes P copnAd) .L ↔
      P.A1dCorr := by sorry

end NegAdPosition.CoLocate
