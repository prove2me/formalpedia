-- Prove2me | Theorems.Thm_IntCapAlloc_OrgChoice_appendix_b1_no_disclosure_of_zero
-- name    : IntCapAlloc.OrgChoice.appendix_b1_no_disclosure_of_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:40:34.977985+00:00
-- url     : https://prove2.me/theorems/a8186135-6853-4cc4-a040-b107d01f04d8
-- title:
--   Appendix B.1, p. 41 — in every equilibrium of the multi-divisional firm, an unprofitable project (θᵢ = 0) is never disclosed
-- statement:
--   Consider the multi-divisional firm with parameters $0 < p < 1$, $X > 1$, $c > 0$, $0 < q < 1$, $\beta > qX$ and $X \ge 1 + c$. In every pure-strategy perfect Bayesian equilibrium $(\sigma, \mu)$, no type discloses an unprofitable project:
--   $$
--   \theta_i = 0 \implies \sigma(\theta_1,\theta_2)_i = ND \qquad \text{for all } (\theta_1,\theta_2) \text{ and } i \in \{1,2\}.
--   $$
--
--   This is the first step of the paper's classification of equilibria (Appendix B.1): it reduces the candidate disclosure strategies to those in which only profitable projects are ever disclosed. It relies on the tie rule (PBE item 5): a manager with $(\theta_1,\theta_2) = (0,0)$ is indifferent among all messages that secure the same $k$.
--
--   Differences from the source:
--   - reading: Appendix B.1 does not restate the parameter space → the standing assumptions of §2 and the focus $X \ge 1 + c$ of §4 (p. 11) are hypotheses; reason: Appendix B identifies the equilibria behind Proposition 2, which assumes $X \ge 1+c$.
--   - reading: PBE item 5 "$d_i^* = ND$ is chosen if $d_i = D$ results in the same payoff" → per coordinate: if a type discloses project $i$, withholding project $i$ alone gives a strictly lower payoff; reason: the rule is stated per project $i$.
--   - reading: item 4 lets λ maximize the manager's payoff → λ = 1 iff $\theta_1 \ge \theta_2$; reason: the paper fixes this rule on p. 11.
--   - reading: equilibria → pure disclosure strategies; reason: Appendix B.1 identifies "the possible pure-strategy equilibrium disclosure choices".
--   - generalization: footnote 7 restricts to sufficiently high β → only $\beta > qX$ is assumed; reason: the game uses β only through $\beta > qX$, so the statement covers the footnote's case.
-- source:
--   Hwang, Internal Capital Allocation, Voluntary Disclosure, and Investment Efficiency, author manuscript (March 2025) of Management Science doi:10.1287/mnsc.2022.01295, p. 41, Appendix B.1, 'I first show that if θi = 0, choosing di = D is not an equilibrium strategy'

import Mathlib
import Definitions.Def_IntCapAlloc_OrgChoice_Model

namespace IntCapAlloc.OrgChoice

/-- Appendix B.1 (p. 41): in every pure-strategy PBE of the multi-divisional firm, no type
discloses a project with θᵢ = 0. -/
theorem appendix_b1_no_disclosure_of_zero (p X c q bet : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (hX : 1 < X) (hc : 0 < c)
    (hq0 : 0 < q) (hq1 : q < 1) (hbet : q * X < bet) (hfocus : 1 + c ≤ X)
    (σ : Profile → Disc) (μ : Belief) (hEq : IsEquilibrium p X c q bet σ μ) :
    ∀ t i, t i = false → σ t i = false := by sorry

end IntCapAlloc.OrgChoice
