-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_lemma_1
-- name    : MarketFreeze.Hetero.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:39.989996+00:00
-- url     : https://prove2.me/theorems/aab25156-30a1-45bc-b3e3-86a41c718f71
-- title:
--   Lemma 1, p. 18 — a buyer screens iff its equity is at least E^het = E^hom − λ(X − p)/(1 + n); the reduction falls in n and rises in λ
-- statement:
--   Under the model assumptions, let $\theta\in[0,\bar\theta]$, $n\ge0$, and $\lambda>0$. For every feasible equity level $E\in[0,I]$, the buyer's screening incentive constraint (A2), with debt $D=I-E$, holds exactly when $E$ reaches the threshold
--
--   $$E\ge E^{\mathrm{het}}(\theta,n)=E^{\mathrm{hom}}(\theta)-\lambda\frac{X-p(n)}{1+n}.$$
--
--   The reduction in required equity is strictly larger at lower $n$, and strictly larger when $\lambda$ rises while all other quantities are fixed. This identifies the minimum equity held by a screening buyer.
--
--   **Formalization Note** The incentive constraint includes both branches of the maximum in (A2); the first branch is inactive under the paper's assumptions.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), Lemma 1, p. 18; proof and equation (A2), p. 35

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem lemma_1 (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 P.θbar)
    (n : ℝ) (hn : 0 ≤ n) :
    (∀ E : ℝ, E ∈ Set.Icc 0 P.I →
      (icRHS P θ E (P.I - E) ≤ icLHS P θ n E (P.I - E) ↔
        Ehet P θ n ≤ E)) ∧
    StrictAntiOn (fun m : ℝ => P.lam * (P.X - price P m) / (1 + m)) (Set.Ici 0) ∧
    (∀ lam' : ℝ, P.lam < lam' →
      P.lam * (P.X - price P n) / (1 + n) <
        lam' * (P.X - price P n) / (1 + n)) := by sorry

end MarketFreeze.Hetero
