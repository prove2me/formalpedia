-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_gap_identity
-- name    : IdentityMgmt.FIA.gap_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:50.509789+00:00
-- url     : https://prove2.me/theorems/84fc7eaf-f2bc-4b00-87d7-ebcb4ab8ac6f
-- title:
--   p. 28 (PDF 32) — under FIA, θ̃ − θ_inf = c(1−βγ)²/(β(1−γ)(1+(1−2β)γ)), linear in the privacy cost
-- statement:
--   In every quasi-linear FIA Markov perfect equilibrium with an interior pivot $\tilde\theta < 1$, the fraction of passive customers who are eventually served is
--   $$\tilde\theta - \theta_{\inf} = \frac{c\,(1-\beta\gamma)^2}{\beta(1-\gamma)\big(1+(1-2\beta)\gamma\big)},$$
--   where $\beta$ is the discount factor, $c$ the privacy cost, $\gamma$ the slope of the cut-off rule and $\theta_{\inf} = K/(1-\gamma)$ the limit of the market-expansion path.
--
--   Since $\gamma$ depends on $\beta$ alone, the served passive share is linear in $c$, which is the paper's statement that the equilibrium number of passive customers who eventually buy is increasing in the privacy cost.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), p. 28 (PDF 32), display after Proposition 1; Online Appendix, OA p. 5 (PDF 59), proof of Proposition 1

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem gap_identity (P : Profile) (hP : P.IsMPE) (hint : P.θt < 1) :
    P.θt - P.θinf =
      P.c * (1 - P.β * P.γ) ^ 2 / (P.β * (1 - P.γ) * (1 + (1 - 2 * P.β) * P.γ)) := by sorry

end IdentityMgmt.FIA
