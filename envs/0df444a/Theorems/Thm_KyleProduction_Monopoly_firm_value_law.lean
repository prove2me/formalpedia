-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_firm_value_law
-- name    : KyleProduction.Monopoly.firm_value_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:29.015101+00:00
-- url     : https://prove2.me/theorems/707918e1-699d-49ba-95dd-7cde17bb2675
-- title:
--   Appendix A, proof of Proposition 1, p. 23 (PDF 24) — given s, Ṽ ∼ N(q(E[a|s] − q), q²ΣaΣθ/(Σa+Σθ))
-- statement:
--   Given the disclosed signal $s$, the demand intercept is $(a\mid s) \sim N\big(E[a|s], \Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)\big)$. For any output quantity $q \in \mathbb R$, the firm value $V = q(a-q)$ is then distributed as
--   $$\tilde V \sim N\!\left(q\,(E[a|s]-q),\ q^2\,\frac{\Sigma_a\Sigma_\theta}{\Sigma_a+\Sigma_\theta}\right),$$
--   and in particular $E[V(q)] = q\,(E[a|s]-q)$.
--
--   The quantity chosen at the production stage moves both the mean and the variance of the firm value. The variance is what the insider trades on, so this is how production feeds into the trading stage.
--
--   **Formalization Note.** At $q = 0$ both sides are the point mass at $0$, a normal law with zero variance.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 23 (PDF 24), Appendix A, proof of Proposition 1; also §2.2, p. 6 (PDF 7)

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

open MeasureTheory ProbabilityTheory

theorem firm_value_law (P : Params) (hS : P.Standing) (q : ℝ) :
    (lawA P).map (firmValue q) =
      gaussianReal (q * (postMean P - q)) (q ^ 2 * postVar P).toNNReal ∧
    expFirmValue P q = q * (postMean P - q) := by sorry

end KyleProduction.Monopoly
