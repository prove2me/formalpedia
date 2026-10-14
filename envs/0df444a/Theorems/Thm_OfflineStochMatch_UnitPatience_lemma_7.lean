-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_lemma_7
-- name    : OfflineStochMatch.UnitPatience.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:34.362666+00:00
-- url     : https://prove2.me/theorems/11cba86d-625d-424b-a620-637d31566d96
-- title:
--   Lemma 7, p. 16 — E[W(v)] ≥ Σ_i w_i z_i ∏_{j<i}(1 − z_j) with edges labelled by decreasing weight
-- statement:
--   Fix $v\in V_2$ and label the edges of $\delta(v)$ from $1$ to $k=|\delta(v)|$ so that $w_1\ge w_2\ge\cdots\ge w_k$, and put $z_i=p_iy_i$. Then the expected weight the algorithm matches at $v$ satisfies
--   $$\mathbb E[W(v)]\ge\sum_{i=1}^{k}w_iz_i\prod_{j=1}^{i-1}(1-z_j).$$
--
--   The right-hand side is exactly the expected weight that greedy-by-weight would collect if the edges of $\delta(v)$ were rounded and activated independently; the lemma says the dependent rounding does no worse.
--
--   **Formalization Note** The labelling is the order $\mathrm{ord}(v)$ ($0$-based in Lean). The lemma's statement does not say $w\ge 0$, but its proof needs it ($w_k-w_{k+1}=w_k\ge 0$) and the section works with a weighted graph; nonnegative weights are carried as a standing hypothesis, together with $p_e\in[0,1]$, LP (3) feasibility of $y$ and the admissibility of the rounding.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 16, Lemma 7

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem lemma_7 {V₁ V₂ E : Type} [Fintype E] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E]
    (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) (v : V₂) :
    ∑ i : Fin (ord v).length,
        w ((ord v).get i) * (p ((ord v).get i) * y ((ord v).get i)) *
          ∏ j ∈ univ.filter (fun j : Fin (ord v).length => j < i),
            (1 - p ((ord v).get j) * y ((ord v).get j))
      ≤ EW w p ord v μ := by sorry

end OfflineStochMatch.UnitPatience
