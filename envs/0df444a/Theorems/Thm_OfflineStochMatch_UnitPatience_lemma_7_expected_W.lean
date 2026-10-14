-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_lemma_7_expected_W
-- name    : OfflineStochMatch.UnitPatience.lemma_7_expected_W
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:29.70299+00:00
-- url     : https://prove2.me/theorems/c12c28e9-1861-4e6c-8c78-cc624bfd0aad
-- title:
--   Proof of Lemma 7, p. 17, first display — E[W(v)] = E[Σ_i w_i Y_i P_i ∏_{j<i}(1 − Y_j P_j)]
-- statement:
--   Fix $v\in V_2$ and label the edges of $\delta(v)$ as $e_1,\dots,e_k$ in the probing order (decreasing weight), writing $w_i,Y_i,P_i$ for the weight, the rounding indicator and the activeness indicator of $e_i$. Then the expected weight matched at $v$ is
--   $$\mathbb E[W(v)]=\mathbb E\Big[\sum_{i=1}^{k}w_iY_iP_i\prod_{j=1}^{i-1}(1-Y_jP_j)\Big].$$
--
--   This identity turns the algorithm's outcome at $v$ (the weight of the first rounded, active edge in decreasing weight order) into an explicit polynomial in the indicators, on which the negative correlation property can act.
--
--   **Formalization Note** The page prints the inner product as $\prod_{i=1}^{i-1}$; it is $\prod_{j=1}^{i-1}$. Labels are $0$-based in Lean ($i:\mathrm{Fin}\,k$, product over $j<i$). The standing hypotheses of §4 (feasible $y$, admissible rounding, $p_e\in[0,1]$, a decreasing-weight order) are carried for context; the identity holds pointwise in $(Y,P)$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 17, proof of Lemma 7, first display

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem lemma_7_expected_W {V₁ V₂ E : Type} [Fintype E] [DecidableEq V₁] [DecidableEq V₂] [DecidableEq E]
    (G : BipGraph V₁ V₂ E) (w p y : E → ℝ) (t : V₂ → ℕ∞)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hy : LPFeasible G p y t)
    (μ : Finset E → ℝ) (hμ : IsRounding G y t μ)
    (ord : V₂ → List E) (hord : IsWeightOrder G w ord) (v : V₂) :
    EW w p ord v μ =
      ∑ Y, μ Y * ∑ P : E → Bool, OfflineStochMatch.InfinitePatience.coinWeight p P *
        ∑ i : Fin (ord v).length, w ((ord v).get i) * YP Y P ((ord v).get i) *
          ∏ j ∈ univ.filter (fun j : Fin (ord v).length => j < i), (1 - YP Y P ((ord v).get j)) := by sorry

end OfflineStochMatch.UnitPatience
