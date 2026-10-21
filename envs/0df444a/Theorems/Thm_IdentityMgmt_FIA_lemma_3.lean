-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_lemma_3
-- name    : IdentityMgmt.FIA.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:53.300428+00:00
-- url     : https://prove2.me/theorems/16b76d25-cd37-4642-83a6-13720a7e4659
-- title:
--   Lemma 3, p. 27 (PDF 31) — under FIA the pivotal customer θ̃ is given by (18)
-- statement:
--   In every quasi-linear FIA Markov perfect equilibrium with an interior pivot $\tilde\theta < 1$ (cut-off rule $\theta_{n+1} = K + \gamma\theta_n$, expectations rule $\Psi(\theta) = C + \lambda\theta$, discount factor $\beta$, privacy cost $c$),
--   $$\tilde\theta = \frac{(-1+\beta)\big(K\beta(1+\gamma) + c(1-\beta\gamma)\big) + K\beta\lambda}{(-1+\beta)\,\beta\,\big(1 + \gamma(\beta(-1+\gamma) - \gamma + \lambda)\big)}. \qquad (18)$$
--
--   It is the pivot indifference condition (20) solved for $\tilde\theta$, and expresses the pivot through the equilibrium coefficients.
--
--   **Formalization Note.** The first sentence of Lemma 3 (the cut-off structure of the privacy decision) is built into the model, which takes the active set to be $[\tilde\theta, 1]$. The hypothesis $\tilde\theta < 1$ selects the case in which (20) holds with equality; at the corner $\tilde\theta = 1$ the paper itself uses $\min\{\cdot, 1\}$.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), p. 27 (PDF 31), Lemma 3, eq. (18); Online Appendix, OA p. 5 (PDF 59), proof of Lemma 3

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem lemma_3 (P : Profile) (hP : P.IsMPE) (hint : P.θt < 1) :
    P.θt =
      ((-1 + P.β) * (P.K * P.β * (1 + P.γ) + P.c * (1 - P.β * P.γ)) + P.K * P.β * P.lam) /
        ((-1 + P.β) * P.β * (1 + P.γ * (P.β * (-1 + P.γ) - P.γ + P.lam))) := by sorry

end IdentityMgmt.FIA
