-- Prove2me | Theorems.Thm_OnlineMatchFrameworks_arrival_bound
-- name    : OnlineMatchFrameworks.arrival_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:31:53.665191+00:00
-- url     : https://prove2.me/theorems/508f6259-a31a-477f-b7f4-87f78251b2ea
-- title:
--   Proof of Lemma 2: the bound per arrival
-- statement:
--   Let $0\le\kappa\le 1$, let the black box be $\kappa$-approximate, and let $x\ge 0$ satisfy (1d). For every available set $A$ and customer $v$,
--   $$
--   \kappa\sum_{u\in U}x_{u,v}p_{u,v}w_u\le\sum_l\mathrm{BB}(A,v)(l)\,\mathrm{star}_v(l)+\sum_{u\notin A}x_{u,v}p_{u,v}w_u .
--   $$
--   This is the step that turns the black-box guarantee into a bound with the LP's per-customer value.
--
--   Differences from the source:
--   - encoding: assigned value at least 0.5κOPT(U_v,v) + 0.5Σ_{U_{-v}} x p w, then (1d) and κ ≤ 1 in the display → the two steps at once, multiplied by 2, with the black box's expected star value for the assigned value; reason: the same inequality for each state (A = U_v) before taking the expectation over U_v
--   - generalization: x an optimal solution of LP (1) → any x ≥ 0 satisfying (1d); reason: the optimal solution is a special case
--   - generalization: patience deterministic (p.11), an arbitrary distribution (§5.2) or item hazard rates (§5.1) → one survival function S_v(l) in [0,1], sublist monotone; reason: the three models satisfy the hypotheses (proved in the sanity file), so each is a special case
--   - reading: StarBB within a factor κ of optimal (pp.5, 14), κ ∈ [0,1] → a PMF over duplicate-free lists of available items with κ·OPT(A,v) ≤ expected star value, for all A, v; reason: the form the proof on p.40 uses; the weight form on p.5 implies it, and a randomized star policy is a mixture of lists
--   - reading: expected size of the matching (p.14), while the setting, LP (1) and the proof use weight → expected weight, w ≥ 0; reason: size is w ≡ 1, so this is the stronger reading
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, Appendix A, proof of Lemma 2, p.40, "After using a κ-approximate"

import Definitions.Def_OnlineMatchFrameworks_BlackBox

open scoped BigOperators

namespace OnlineMatchFrameworks

/-- **The bound per arrival.** arXiv:1907.03963v6, Appendix A, proof of Lemma 2, p.40, "After using a
κ-approximate (κ ≤ 1) black box" and the step marked (1d). For an available set `A`, customer `v`,
with `U_{-v} = Aᶜ`:
`κ ∑_{u ∈ U} x_{u,v} p_{u,v} w_u ≤ E[star_v(BB)] + ∑_{u ∈ Aᶜ} x_{u,v} p_{u,v} w_u`. -/
theorem arrival_bound {U V : Type*} [DecidableEq U] [Fintype U]
    (G : Instance U V) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (BB : Finset U → V → PMF (Policy U)) (hBB : G.IsKappaApprox κ BB)
    (x : U → V → ℝ) (hx0 : ∀ u v, 0 ≤ x u v)
    (hx : ∀ (U' : Finset U) (v : V), ∑ u ∈ U', x u v * G.p u v * G.w u ≤ G.starOpt U' v)
    (A : Finset U) (v : V) :
    κ * ∑ u, x u v * G.p u v * G.w u ≤
      ∑ l : Policy U, (BB A v l).toReal * G.starValue v l.1 +
        ∑ u ∈ Aᶜ, x u v * G.p u v * G.w u := by sorry

end OnlineMatchFrameworks
