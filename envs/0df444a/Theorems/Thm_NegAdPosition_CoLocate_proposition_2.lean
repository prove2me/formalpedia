-- Prove2me | Theorems.Thm_NegAdPosition_CoLocate_proposition_2
-- name    : NegAdPosition.CoLocate.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:32.363239+00:00
-- url     : https://prove2.me/theorems/3a23d9ff-33b0-4ca9-bf9e-8837ab8d27ed
-- title:
--   Proposition 2, p. 16 (corrected region) — with negative ads permitted, a PBE exists where the entrant co-locates and both firms prioritize positive ads; apart, negative-ad wars
-- statement:
--   Consider the entry, positioning and advertising game in which both positive and negative advertising are permitted. Assume the standing assumptions ($\delta, \Pi, \beta > 0$, $\sigma_\Pi, \sigma_\beta, \rho \in (0,1)$, $\underline\gamma < \bar\gamma$, $\sigma_\Pi\Pi = \sigma_\beta\beta$), Assumption 1′ ($\underline\gamma < -\Pi$ and $\bar\gamma > \delta + \sigma_\Pi\Pi + (1-\sigma_\beta)\beta$), and
--   $$\beta > (1-\sigma_\Pi)\Pi + \delta, \quad \bar\gamma + \sigma_\beta\beta \ge (1-\sigma_\Pi)\Pi + \delta, \quad \Pi > (1-\rho)(1-\sigma_\beta)\beta, \quad \delta < \Pi + \sigma_\beta\beta,$$
--   together with the corrected location condition (A1d′). Then there is a perfect Bayesian equilibrium (entrant location, advertising strategies at both locations, consumer beliefs) such that
--
--   1. the entrant co-locates with the incumbent, $x_2 = L$;
--   2. after co-location, both firms prioritize positive advertising: a firm whose product has the positive attribute advertises it, whatever the rival's type;
--   3. off the equilibrium path, where the entrant locates apart, a firm that can advertise both its own positive attribute and the rival's negative attribute, and whose rival can itself advertise (a strong opponent), runs negative advertising.
--
--   The proposition says that allowing negative advertising can lead an entrant to give up product differentiation: co-location makes the products' attributes correlated, so an attack on the rival's negative attribute would also hurt the attacker, and this spillover keeps both firms on positive advertising.
--
--   **Formalization Note.** The page states the existence with no hypotheses; its proof restricts to the region (A1a)–(A1d). That printed region is not sufficient: at $\delta = 1/2$, $\Pi = \beta = 2$, $\sigma_\Pi = \sigma_\beta = 1/2$, $\rho = 1/4$, $\underline\gamma = -3$, $\bar\gamma = 7/2$ every printed condition holds, yet the entrant's expected demand is $479/832$ when co-locating and $127/208$ when locating apart. The corrected region uses $\underline\gamma < -\Pi$ (printed $\underline\gamma < \Pi$), the added condition $\delta < \Pi + \sigma_\beta\beta$ (excluding the region of Lemma 1, which the proof wrongly says is ruled out), $\rho < 1$, and (A1d′) in place of (A1d). The equilibrium is required to satisfy all PBE conditions: truthful ads, beliefs that are probability mass functions consistent with the ads, Bayes' rule on every outcome of positive probability, best responses in the advertising sub-game at both locations for every type profile, and an optimal location.
-- source:
--   Bostanci, Yildirim & Jerath, Negative Advertising and Competitive Product Positioning, authors' manuscript (Nov. 2021; Management Science 2023, doi:10.1287/mnsc.2022.4439), p. 16 (PDF 16), Proposition 2; proof pp. A3–A6 (PDF 46–49), conditions (A1a)–(A1d) (corrected)

import Mathlib
import Definitions.Def_NegAdPosition_CoLocate_Model

namespace NegAdPosition.CoLocate

theorem proposition_2 (P : Params) (hS : P.Standing) (hA1 : P.Assumption1)
    (ha : P.A1a) (hb : P.A1b) (hc : P.A1c) (hδ : P.δ < P.Pi + P.σB * P.β) (hd : P.A1dCorr) :
    ∃ σ : Profile, IsPBE P σ ∧ σ.x2 = Loc.L ∧
      (∀ i θ, θ.P i = true → σ.ad i Loc.L θ = Ad.pos) ∧
      (∀ i θ, θ.P i = true → θ.N i.other = true → (θ.P i.other = true ∨ θ.N i = true) →
        σ.ad i Loc.R θ = Ad.neg) := by sorry

end NegAdPosition.CoLocate
