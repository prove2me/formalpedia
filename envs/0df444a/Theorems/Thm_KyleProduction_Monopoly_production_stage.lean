-- Prove2me | Theorems.Thm_KyleProduction_Monopoly_production_stage
-- name    : KyleProduction.Monopoly.production_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:34.652653+00:00
-- url     : https://prove2.me/theorems/edc37f30-c523-4d48-974b-4dd55e80dbed
-- title:
--   Appendix A, proof of Proposition 1, (34), p. 24 (PDF 25) — q̂ = (2ωE[a|s] + √(ΣuΣaΣθ/(Σa+Σθ)))/(4ω) uniquely maximizes the manager's objective
-- statement:
--   Assume the standing assumptions and $E[a|s] > 0$, and write $\kappa = \sqrt{\Sigma_u\Sigma_a\Sigma_\theta/(\Sigma_a+\Sigma_\theta)}$. The manager's reduced objective at the production stage is
--   $$E[\Pi] + \omega E[V] = \omega\,q\,(E[a|s]-q) + \frac{|q|}{2}\,\kappa .\tag{34}$$
--   Over all $q \in \mathbb R$, it has the unique maximizer
--   $$\hat q = \frac{2\omega E[a|s] + \kappa}{4\omega} = \frac12 E[a|s] + \frac{1}{4\omega}\kappa .$$
--   Every other $q$ gives a strictly smaller value.
--
--   This is the first-order condition of the proof of Proposition 1, together with the check that it gives the global maximum.
--
--   **Formalization Note.** The page prints the left side of (34) as $E[\Pi] + \omega[V]$, which means $\omega E[V]$. It writes $\hat q/2$ for $|q|/2$, having positive quantities in mind; see the trading-profit milestone. The hypothesis $E[a|s] > 0$ makes precise footnote 7's "$m_a$ is sufficiently large". On $q \le 0$ the objective peaks at $E[a|s]/2 - \kappa/(4\omega)$ or at $0$, and it stays strictly below $\omega\hat q^2$ exactly when $E[a|s] > 0$.
-- source:
--   Chen and Jorgensen, Insider Trading, Competition, and Real Activities Manipulation, SSRN 2358668 (version of February 2016), p. 24 (PDF 25), Appendix A, proof of Proposition 1, (34) and the first-order condition after it; footnote 7, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_KyleProduction_Monopoly_Model

namespace KyleProduction.Monopoly

theorem production_stage (P : Params) (hS : P.Standing) (hm : 0 < postMean P) (q : ℝ)
    (hq : q ≠ qHat P) :
    P.ω * (q * (postMean P - q)) + |q| / 2 * kappa P <
      P.ω * (qHat P * (postMean P - qHat P)) + |qHat P| / 2 * kappa P := by sorry

end KyleProduction.Monopoly
