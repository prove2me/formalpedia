-- Prove2me | Theorems.Thm_KellyStochasticNetworks_alpha_fair_one_proportionally_fair
-- name    : KellyStochasticNetworks.alpha_fair_one_proportionally_fair
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T16:51:37.677461+00:00
-- url     : https://prove2.me/theorems/586eb104-c3f3-4076-81f4-b65d6c027211
-- title:
--   Section 8.2 — at $\alpha = 1$ the allocation is weighted proportionally fair
-- statement:
--   At $\alpha = 1$ the weighted $\alpha$-fair objective is $\sum_r w_r n_r \log X_r$, which is the
--   objective of $\mathrm{network}(A,C;\,w\!\cdot\!n)$ — the network problem of section 7.1 with
--   weights $w_r n_r$. By Proposition 7.4, published in mission VII of this series, solving that
--   problem is the same as being weighted proportionally fair with those weights. So for a positive
--   feasible aggregate rate vector $X$,
--   $$X \text{ maximizes } \sum_r w_r n_r \log X_r \text{ over the feasible set}
--     \iff \sum_r w_r n_r\,\frac{Y_r - X_r}{X_r} \le 0 \text{ for every feasible } Y .$$
--
--   This is the anchor of the $\alpha$-family in the fairness notions of Chapter 7: $\alpha = 1$ is
--   weighted proportional fairness, and hence, by Remark 7.5, also the Nash bargaining solution and a
--   market-clearing equilibrium. The other anchors of the family are limits rather than exact
--   identities — throughput maximization as $\alpha \to 0$, max-min fairness as $\alpha \to \infty$ —
--   and are listed under contributions welcome.
--
--   **Formalization Note** The weights carried into Proposition 7.4 are the products $w_r n_r$, which
--   is why positivity of the flow counts is assumed. The maximum is over the feasible set intersected
--   with the positive orthant, since $\log 0$ is not a real number; the fairness condition is
--   quantified over all feasible $Y$, including boundary points, exactly as in Chapter 7.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 188 (PDF p. 196): 'The form of an alpha-fair rate allocation captures several of the fairness definitions we have seen earlier. As alpha -> 0 and with w_r = 1 the total throughput, sum_r n_r x_r, approaches its maximum. If alpha = 1 then, from Proposition 7.4, the rates x_r are weighted proportionally fair. If alpha = 2 and w_r = 1/T_r^2 then the rates x_r are TCP fair, i.e. they are of the form (7.9). As alpha -> infinity and with w_r = 1 the rates x_r approach max-min fairness.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion
import Definitions.Def_KellyStochasticNetworks_FlowLevel

namespace KellyStochasticNetworks

theorem alpha_fair_one_proportionally_fair {J R : ℕ} (A : Fin J → Fin R → ℝ) (C : Fin J → ℝ)
    (w n : Fin R → ℝ) (hA : ∀ j r, 0 ≤ A j r) (hw : ∀ r, 0 < w r) (hn : ∀ r, 0 < n r)
    (X : Fin R → ℝ) (hXpos : ∀ r, 0 < X r) (hXfeas : X ∈ networkFeasible A C) :
    IsMaxOn (alphaFairObjective w n 1) (networkFeasible A C ∩ {Y | ∀ r, 0 < Y r}) X
      ↔ ∀ Y ∈ networkFeasible A C, (∑ r, w r * n r * ((Y r - X r) / X r)) ≤ 0 := by sorry

end KellyStochasticNetworks
