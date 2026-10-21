-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq15LHS_strictMonoOn
-- name    : MarketFreeze.Hetero.eq15LHS_strictMonoOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:48.863786+00:00
-- url     : https://prove2.me/theorems/6339e1e0-8e73-42c7-950d-1b466228bdd0
-- title:
--   Proof of Proposition 2, p. 37 — the LHS of (15) is strictly increasing in n, from the sole-buyer to the sole-seller gain
-- statement:
--   Let $X>I$, $\lambda>0$, $\psi>0$ and $\theta<1$. The left-hand side of the equilibrium condition (15),
--   $$L(n)=\lambda(X-I)\left[\frac{1-\theta}{2}\cdot\frac{n-1}{n+1}-\frac{\psi}{(n+1)^2}\right],$$
--   is strictly increasing in $n\ge0$, equals $-\lambda(X-I)\big[\tfrac{1-\theta}{2}+\psi\big]$ at $n=0$ and tends to $\lambda(X-I)\tfrac{1-\theta}{2}$ as $n\to\infty$. The two end values are the sole buyer's and the sole seller's gains from deviating; since the right-hand side $\Delta\pi^{hom}(\theta)$ does not depend on $n$, (15) has at most one root, and it has one exactly when $\Delta\pi^{hom}(\theta)$ lies strictly between them.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), proof of Proposition 2 (Appendix A), p. 37, "The LHS of (15) is monotonically increasing in n"; end values p. 36

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq15LHS_strictMonoOn (P : Params) (h0 : Standing P) (hXI : P.I < P.X)
    (hlam : 0 < P.lam) (θ : ℝ) (hθ : θ < 1) :
    StrictMonoOn (eq15LHS P θ) (Set.Ici 0) ∧
    eq15LHS P θ 0 = -(P.lam * (P.X - P.I) * ((1 - θ) / 2 + P.ψ)) ∧
    Filter.Tendsto (eq15LHS P θ) Filter.atTop
      (nhds (P.lam * (P.X - P.I) * (1 - θ) / 2)) := by sorry

end MarketFreeze.Hetero
