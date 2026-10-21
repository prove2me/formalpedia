-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_lemma_2_5_a
-- name    : LiqProvision.Oligopoly.lemma_2_5_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:33.011848+00:00
-- url     : https://prove2.me/theorems/4627dd0d-4ff3-4db8-afc2-fbafa8237c7b
-- title:
--   Lemma 2.5(a), p. 5 — for K ≥ 2 dealers a price schedule is admissible iff it is strictly convex
-- statement:
--   Let $K\ge2$ and $\gamma_c>0$. A price schedule $P$ (continuous, $P(0)=0$, twice continuously differentiable off $0$) is admissible for $K$ dealers, i.e. the client's problem
--   $$\max_{\mathbf n\in\mathbb R^K}\ y\sum_k n_k-\sum_k P(n_k)-\frac{\gamma_c}{2}\Big(\sum_k n_k\Big)^2$$
--   has a unique maximizer for every type $y$, if and only if $P$ is strictly convex on $\mathbb R$.
--
--   With competition, admissibility is therefore the convexity condition usually imposed a priori; it is used to show that equilibrium marginal prices are increasing.
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. The proof in the paper (pp. 14–15) is labelled "(b)"; it proves this statement (a).
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 5, Lemma 2.5(a); proof pp. 14–15

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
theorem lemma_2_5_a (M : Params) (hK : 2 ≤ M.K) (hγc : 0 < M.γc) (P : ℝ → ℝ) :
    Admissible M P ↔ IsPriceSchedule P ∧ StrictConvexOn ℝ Set.univ P := by sorry
end LiqProvision.Oligopoly
