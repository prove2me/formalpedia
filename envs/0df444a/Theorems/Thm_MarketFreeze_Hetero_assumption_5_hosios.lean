-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_assumption_5_hosios
-- name    : MarketFreeze.Hetero.assumption_5_hosios
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:42.186498+00:00
-- url     : https://prove2.me/theorems/31223d24-8b9c-4da9-b093-0492592322a7
-- title:
--   Assumption 5, p. 12 — α(n)/n = λ/(1+n), β = nα′(n)/α(n) = 1/(1+n), 1 − β = n/(1+n)
-- statement:
--   Under the matching technology of Assumption 5, $\alpha(n)=\lambda n/(1+n)$ with $\lambda>0$, for every market tightness $n>0$:
--   $$\frac{\alpha(n)}{n}=\frac{\lambda}{1+n},\qquad \beta=\frac{n\,\alpha'(n)}{\alpha(n)}=\frac{1}{1+n},\qquad 1-\beta=\frac{n}{1+n}.$$
--   So a buyer meets a seller with probability $\lambda/(1+n)$, and the buyer's bargaining power, which the paper sets equal to the elasticity of the matching function, is $1/(1+n)$. These identities justify the closed forms of the price (13) and of the buyer's equity (14).
--
--   **Formalization Note** Pure calculus: none of Assumptions 1–4 is needed. $\alpha'$ is `deriv`.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), Assumption 5, p. 12

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem assumption_5_hosios (P : Params) (hlam : 0 < P.lam) (n : ℝ) (hn : 0 < n) :
    alpha P n / n = P.lam / (1 + n) ∧
    n * deriv (alpha P) n / alpha P n = beta n ∧
    1 - beta n = n / (1 + n) := by sorry

end MarketFreeze.Hetero
