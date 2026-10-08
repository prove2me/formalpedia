-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_lemma_4_2
-- name    : GivenDegreeSeq.MLE.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:19.327402+00:00
-- url     : https://prove2.me/theorems/f6873542-12cd-4177-864d-b78938ccd174
-- title:
--   Lemma 4.2 — with probability $\ge 1-2n^{-2}$ the observed degrees satisfy the hypotheses of Lemma 4.1
-- statement:
--   Let $L\ge 0$. There are constants $C>0$ and $c_1,c_2\in(0,1)$, depending only on $L$, and for every $c\in(0,1)$ a constant $c_3\in(0,1)$, depending only on $L$ and $c$, such that the following holds. Let $n>C$, let $\beta\in\mathbb R^n$ with $|\beta_i|\le L$ for all $i$, and let $G$ be drawn from $\mathbb P_\beta$ with degree sequence $d_1,\dots,d_n$. Then with probability at least $1-2n^{-2}$:
--
--   1. $c_2(n-1)\le d_i\le c_1(n-1)$ for all $i$, and
--   2. for every $B\subseteq\{1,\dots,n\}$ with $|B|\ge cn$,
--   $$\sum_{j\notin B}\min\{d_j,|B|\}+|B|(|B|-1)-\sum_{i\in B}d_i\ \ge\ \Big(c_3-\sqrt{\tfrac{6\log n}{n}}\Big)\,n^2.$$
--
--   Together with Lemma 4.1 this shows that a typical realization of the $\beta$-model has an MLE in a bounded box.
--
--   **Formalization Note** The paper writes $L:=\max_i|\beta_i|$; here $L$ is any bound $|\beta_i|\le L$, which is equivalent under the paper's convention that constants depending on $L$ are bounded on compact sets. The paper's infimum form is written as the bound for every admissible $B$ (a finite nonempty family). The probability is the $\mathbb P_\beta$-measure of the event, compared with $\max(0,1-2n^{-2})$ in $[0,\infty]$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 20, Lemma 4.2 (proof pp. 20–21)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_BetaModel

namespace GivenDegreeSeq.MLE

/-- Lemma 4.2, p. 20. For every `L ≥ 0` there are constants `C > 0` and `c₁, c₂ ∈ (0, 1)`,
depending only on `L`, and for every `c ∈ (0, 1)` a constant `c₃ ∈ (0, 1)` depending only on
`L` and `c`, such that for every `n > C` and every `β ∈ ℝⁿ` with `|β_i| ≤ L` for all `i`, with
`P_β`-probability at least `1 − 2n⁻²` the degree sequence `d` of `G` satisfies
`c₂(n − 1) ≤ d_i ≤ c₁(n − 1)` for all `i`, and
`Σ_{j ∉ B} min{d_j, |B|} + |B|(|B| − 1) − Σ_{i ∈ B} d_i ≥ (c₃ − √(6 log n / n)) n²`
for every `B` with `|B| ≥ cn`. -/
theorem lemma_4_2 :
    ∀ L : ℝ, 0 ≤ L → ∃ C c₁ c₂ : ℝ, 0 < C ∧ c₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ c₂ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ c ∈ Set.Ioo (0 : ℝ) 1, ∃ c₃ ∈ Set.Ioo (0 : ℝ) 1,
        ∀ n : ℕ, C < (n : ℝ) → ∀ β : Fin n → ℝ, (∀ i, |β i| ≤ L) →
          ENNReal.ofReal (1 - 2 / (n : ℝ) ^ 2) ≤
            betaModel β {G | (∀ i, c₂ * ((n : ℝ) - 1) ≤ deg G i ∧ deg G i ≤ c₁ * ((n : ℝ) - 1)) ∧
              ∀ B : Finset (Fin n), c * (n : ℝ) ≤ (B.card : ℝ) →
                (c₃ - Real.sqrt (6 * Real.log n / n)) * (n : ℝ) ^ 2 ≤ slack (deg G) B} := by sorry

end GivenDegreeSeq.MLE
