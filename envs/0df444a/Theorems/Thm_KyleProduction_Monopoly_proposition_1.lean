-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_proposition_1
-- name    : KyleProduction.Monopoly.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:38.917531+00:00
-- url     : https://prove2.me/theorems/69af19f0-8f5c-4e1c-976a-9fcd7982c6d6
-- title:
--   Proposition 1, p. 7 (PDF 8) — unique linear equilibrium: q̂ = E[a|s]/2 + (1/(4ω))√(ΣuΣaΣθ/(Σa+Σθ)) and the Kyle coefficients α, β, µ, λ
-- statement:
--   Consider a monopoly with subsequent insider trading. The manager first chooses an output quantity $q \in \mathbb R$, given the disclosed signal $s$. He then trades the firm's stock in a one-shot Kyle market, using a linear demand $d(V) = \alpha + \beta V$ against a market maker with a linear, efficient price $P(D) = \mu + \lambda D = E[V\mid D]$. Write $E[a|s] = (\Sigma_a s + \Sigma_\theta m_a)/(\Sigma_a + \Sigma_\theta)$. Assume the standing assumptions $\Sigma_a, \Sigma_\theta, \Sigma_u > 0$, $0 < \omega \le 1$, and $E[a|s] > 0$.
--
--   Then there is exactly one linear equilibrium. The trading stage at $\hat q$ is a linear equilibrium, and $\hat q$ maximizes $\omega E[V(q)] + E[\Pi(q)]$ against every quantity followed by any linear equilibrium of its own trading stage. It is given by
--   $$\alpha = -\frac{\sqrt{\Sigma_u}}{\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}}\big(E[a|s]-\hat q\big),\qquad \beta = \frac{\sqrt{\Sigma_u}}{\hat q\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}}},$$
--   $$\mu = \hat q\,\big(E[a|s]-\hat q\big),\qquad \lambda = \frac{\hat q}{2\sqrt{\Sigma_u}}\sqrt{\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}},$$
--   and
--   $$\hat q = \frac12\,E[a|s] + \frac{1}{4\omega}\sqrt{\frac{\Sigma_u\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}} .$$
--
--   Without insider trading the manager would produce $q^* = \tfrac12 E[a|s]$ (§2.1). So $\hat q = q^* + \frac{1}{4\omega}\sqrt{\Sigma_u\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)}$ is strictly larger. The prospect of insider trading leads the manager to overproduce, because his expected trading gains grow with the scale of production, and the distortion shrinks as his stake $\omega$ grows.
--
--   **Formalization Note.** The statement is an equivalence: a pair (quantity, strategies) is an equilibrium if and only if it equals the displayed one. This carries existence, uniqueness and every closed form at once. The hypothesis $E[a|s] > 0$ is not printed in the proposition. It makes precise footnote 7 ("we assume $m_a$ is sufficiently large"): over all real quantities the reduced objective is $\omega q(E[a|s]-q) + \tfrac{|q|}{2}\kappa$, and $\hat q$ is its unique maximizer exactly when $E[a|s] > 0$. The bound $\omega \le 1$ is the paper's standing assumption and is kept, although the result does not use it.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 7 (PDF 8), Proposition 1; footnote 7, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem proposition_1 (P : Params) (hS : P.Standing) (hm : 0 < postMean P)
    (q : ℝ) (e : LinStrat) :
    IsEquilibrium P q e ↔ (q = qHat P ∧ e = eqStrat P (qHat P)) := by sorry

end KyleProduction.Monopoly
