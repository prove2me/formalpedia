-- Prove2me | Theorems.Thm_IdentityMgmt_FIA_lemma_2
-- name    : IdentityMgmt.FIA.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:51.804566+00:00
-- url     : https://prove2.me/theorems/d5760eef-8ed3-4ece-914a-102abd2d14da
-- title:
--   Lemma 2, p. 26 (PDF 30) — FIA: λ = β(1−β)(γ−γ²)/(1−βγ), C = −βKγ(1−β)/(1−βγ), and an MPE exists
-- statement:
--   Consider the FIA identity-management game with discount factor $\beta$, cut-off rule $\theta_{n+1} = K + \gamma\theta_n$ and expectations rule $\Psi(\theta) = C + \lambda\theta$.
--
--   1. In every quasi-linear Markov equilibrium (arbitrage equation (8) and Euler condition (16)–(17) at every state, standing assumptions $0<\beta<1$, $0\le\gamma<1$, $0 \le \theta_{\inf} \le \tilde\theta \le 1$), the coefficients satisfy
--   $$\lambda = \frac{\beta(1-\beta)(\gamma-\gamma^2)}{1-\beta\gamma}, \qquad C = -\beta K\,\frac{\gamma(1-\beta)}{1-\beta\gamma}.$$
--   2. For every $\beta \in (0,1)$ and every privacy cost $c \ge 0$ there is a quasi-linear FIA Markov perfect equilibrium with these $\beta$ and $c$ (including the pivot condition (20)).
--
--   The coefficient relations are the first step of the paper's equilibrium construction; the existence part shows that the equilibrium notion of the mission is not empty.
--
--   **Formalization Note.** The page states existence "for a given value of $\tilde\theta$". With $\tilde\theta$ fixed arbitrarily, feasibility $\theta_{\inf} \le \tilde\theta$ fails for small $\tilde\theta$, so existence is stated for the full MPE, with the pivot determined in equilibrium, for every $\beta$ and $c$; this is the existence Proposition 1 needs.
-- source:
--   Laussel, Long & Resende, Profit Effects of Consumers' Identity Management: A Dynamic Model, CIRANO working paper 2021s-29 (24 Aug. 2021), p. 26 (PDF 30), Lemma 2; Online Appendix, OA pp. 3–4 (PDF 57–58), eqs. (27), (28)

import Mathlib
import Definitions.Def_IdentityMgmt_FIA_Model

namespace IdentityMgmt.FIA

theorem lemma_2 :
    (∀ P : Profile, P.IsMarkovEq →
      P.lam = P.β * (1 - P.β) * (P.γ - P.γ ^ 2) / (1 - P.β * P.γ) ∧
      P.C = -P.β * P.K * (P.γ * (1 - P.β) / (1 - P.β * P.γ))) ∧
    (∀ β c : ℝ, 0 < β → β < 1 → 0 ≤ c →
      ∃ P : Profile, P.β = β ∧ P.c = c ∧ P.IsMPE) := by sorry

end IdentityMgmt.FIA
