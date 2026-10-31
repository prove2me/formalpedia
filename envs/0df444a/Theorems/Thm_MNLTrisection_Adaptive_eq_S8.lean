-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_eq_S8
-- name    : MNLTrisection.Adaptive.eq_S8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:10.544044+00:00
-- url     : https://prove2.me/theorems/7cf91955-059d-4877-8639-44dca880d854
-- title:
--   Eqs. (S4), (S8), Supplement p. 2 (PDF 21) — the jump F(θ) − F(θ⁺) of the revenue potential at a revenue level
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Let $F(\theta) = R(\{i : r_i \ge \theta\})$ and let $F(\theta^+) = \lim_{y \to \theta^+} F(y)$ be its right limit. For every real $\theta$,
--   $$F(\theta^+) = R(\{i : r_i > \theta\})$$
--   and
--   $$F(\theta) - F(\theta^+) = \frac{\sum_{r_i = \theta} v_i}{1 + \sum_{r_i \ge \theta} v_i}\,\big[\theta - F(\theta^+)\big].$$
--
--   The identity relates the jump of $F$ at $\theta$ to the position of $F(\theta^+)$ relative to the diagonal; it drives Lemmas 3 and 4.
--
--   **Formalization Note** The page derives the display "for any $\theta \ge \theta^*$" but it is an algebraic identity valid for every $\theta$, and the proof of Lemma 4 uses it below $\theta^*$; it is stated for every $\theta$. $F(\theta^+)$ is Mathlib's `Function.rightLim`.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, Supplement p. 2 (PDF 21), proof of Lemma 3, Eqs. (S4)–(S8)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Eqs. (S4) and (S8)** (Supplement p. 2, proof of Lemma 3). For every `θ`, the right limit
`F(θ⁺)` is `R({i : r_i > θ})`, and
`F(θ) − F(θ⁺) = (∑_{r_i = θ} v_i)/(1 + ∑_{r_i ≥ θ} v_i) · [θ − F(θ⁺)]`. -/
theorem eq_S8 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (θ : ℝ) :
    Function.rightLim (F v r) θ = rev v r (Finset.univ.filter (fun i => θ < r i)) ∧
      F v r θ - Function.rightLim (F v r) θ =
        (∑ i ∈ Finset.univ.filter (fun i => r i = θ), v i) /
            (1 + ∑ i ∈ Finset.univ.filter (fun i => θ ≤ r i), v i) *
          (θ - Function.rightLim (F v r) θ) := by sorry

end MNLTrisection.Adaptive
