-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_insider_best_response
-- name    : KyleProduction.Monopoly.insider_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:24.935703+00:00
-- url     : https://prove2.me/theorems/a3a27c65-7489-4d23-88db-7f800e63d883
-- title:
--   Appendix A, proof of Proposition 1, p. 23 (PDF 24) — the insider's payoff is (V − µ − λd)d and its maximizer is d = −µ/(2λ) + V/(2λ)
-- statement:
--   Fix a linear pricing rule $P(y) = \mu + \lambda y$ and a realized firm value $V$. The insider's expected profit from submitting demand $d$ is
--   $$E\big[(V - \mu - \lambda(d + \tilde u))\,d\big],\qquad \tilde u \sim N(0,\Sigma_u).$$
--   It equals $(V - \mu - \lambda d)\,d$ for every $d \in \mathbb R$. If moreover $\lambda > 0$, a demand $d$ maximizes this profit over $\mathbb R$ if and only if
--   $$d = -\frac{\mu}{2\lambda} + \frac{1}{2\lambda}V .$$
--
--   So the insider's best response to a linear price is linear in $V$, with $\alpha = -\mu/(2\lambda)$ and $\beta = 1/(2\lambda)$. This is the insider's half of the Kyle trading stage.
--
--   **Formalization Note.** The standing assumptions of §2 are carried as a hypothesis, although only $E[\tilde u] = 0$ is needed. The paper takes $\lambda > 0$ for granted when it sets the first-order condition to zero; here it is an explicit hypothesis of the second clause.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 23 (PDF 24), Appendix A, proof of Proposition 1, first paragraph

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem insider_best_response (P : Params) (hS : P.Standing) (e : LinStrat) (v : ℝ) :
    (∀ d : ℝ, insiderPayoff P e v d = (v - e.μ - e.lam * d) * d) ∧
    (0 < e.lam → ∀ d : ℝ,
      ((∀ d' : ℝ, insiderPayoff P e v d' ≤ insiderPayoff P e v d) ↔
        d = -e.μ / (2 * e.lam) + v / (2 * e.lam))) := by sorry

end KyleProduction.Monopoly
