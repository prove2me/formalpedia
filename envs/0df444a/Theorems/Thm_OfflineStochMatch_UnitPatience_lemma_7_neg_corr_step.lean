-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_lemma_7_neg_corr_step
-- name    : OfflineStochMatch.UnitPatience.lemma_7_neg_corr_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:39.103923+00:00
-- url     : https://prove2.me/theorems/44271655-a4d9-4727-aaff-799d79c83194
-- title:
--   Proof of Lemma 7, p. 17, fourth display — E[∏_{j≤i}(1 − Y_j P_j)] ≤ ∏_{j≤i}(1 − y_j p_j)
-- statement:
--   Fix $v\in V_2$ and label the edges of $\delta(v)$ as $e_1,\dots,e_k$ in decreasing order of weight. Let the rounded indicators $Y_j$ come from a rounding with marginals $\Pr[Y_j=1]=y_j$ and the negative correlation property (2) on $\delta(v)$, and let the activeness indicators $P_j\sim\mathrm{Bernoulli}(p_j)$ be independent of each other and of the rounding. Then for every $i\in\{0,1,\dots,k\}$,
--   $$\mathbb E\Big[\prod_{j=1}^{i}(1-Y_jP_j)\Big]\le\prod_{j=1}^{i}(1-y_jp_j).$$
--
--   This is the step where the negative correlation of the dependent rounding enters: the probability that none of the first $i$ edges is both rounded and active is at most what it would be under independence.
--
--   **Formalization Note** The prefix $\{1,\dots,i\}$ is the set of Lean indices $j$ with $j<i$ ($0$-based). The hypotheses are the standing ones of §4: $w_e\ge 0$, $p_e\in[0,1]$, $y$ feasible for LP (3), $\mu$ an admissible rounding (including (2) for $b\in\{0,1\}$ on the rounded indicators), and $\mathrm{ord}(v)$ a decreasing-weight order of $\delta(v)$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 17, proof of Lemma 7, fourth display (uses Eq. (2), p. 6)

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem lemma_7_neg_corr_step {V₁ V₂ E : Type} [Fintype E] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E]
    (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hw : ∀ e, 0 ≤ w e) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) (v : V₂)
    (i : ℕ) (hi : i ≤ (ord v).length) :
    ∑ Y, μ Y * ∑ P : E → Bool, OfflineStochMatch.InfinitePatience.coinWeight p P *
        ∏ j ∈ univ.filter (fun j : Fin (ord v).length => j.val < i), (1 - YP Y P ((ord v).get j))
      ≤ ∏ j ∈ univ.filter (fun j : Fin (ord v).length => j.val < i),
          (1 - y ((ord v).get j) * p ((ord v).get j)) := by sorry

end OfflineStochMatch.UnitPatience
