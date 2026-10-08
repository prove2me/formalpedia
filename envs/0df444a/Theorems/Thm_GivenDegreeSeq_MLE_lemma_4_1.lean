-- Prove2me | Theorems.Thm_GivenDegreeSeq_MLE_lemma_4_1
-- name    : GivenDegreeSeq.MLE.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:33.407005+00:00
-- url     : https://prove2.me/theorems/5b7d481d-1512-4ed1-832a-81939540280a
-- title:
--   Lemma 4.1 — under an Erdős–Gallai slack of order $n^2$, the MLE exists with $|\hat\beta|_\infty\le c_4(c_1,c_2,c_3)$
-- statement:
--   There is a function $c_4(c_1,c_2,c_3)$ of $c_1,c_2\in(0,1)$ and $c_3>0$ alone (not of $n$ or $d$), bounded on every compact subset of $(0,1)\times(0,1)\times(0,\infty)$, with the following property. Let $c_1,c_2\in(0,1)$ and $c_3>0$. Let $n\ge 0$ and let $d=(d_1,\dots,d_n)$ lie in the closure $\overline{\mathcal R}$ of the set of $\beta$-model expected degree sequences. Suppose
--
--   1. $c_2(n-1)\le d_i\le c_1(n-1)$ for all $i$, and
--   2. for every $B\subseteq\{1,\dots,n\}$ with $|B|\ge c_2^2 n$,
--   $$\sum_{j\notin B}\min\{d_j,|B|\}+|B|(|B|-1)-\sum_{i\in B}d_i\ \ge\ c_3\,n^2.$$
--
--   Then the ML equations (3) have a solution $\hat\beta$ with $|\hat\beta|_\infty\le c_4(c_1,c_2,c_3)$.
--
--   The lemma is a quantitative "tightness" statement for the MLE, related to the Erdős–Gallai characterization of degree sequences: a uniform margin in the Erdős–Gallai inequalities on large sets forces the MLE to exist and to stay in a bounded box whose size does not grow with $n$.
--
--   **Formalization Note** The paper's $\frac{1}{n^2}\inf_{|B|\ge c_2^2 n}\{\cdots\}\ge c_3$ is written as the bound for every such $B$; the family is finite and nonempty ($B=\{1,\dots,n\}$ qualifies), so the two are equivalent. $|\hat\beta|_\infty$ is the sup norm. The function $c_4$ is chosen before $n$ and $d$, and its boundedness on compact sets is the meaning §4 (p. 16) gives to "a constant that depends only on $c_1,c_2,c_3$" ("a function of $a,b,\dots$ that is bounded away from $0$ and $\infty$ on compact subsets of the domain"); for an upper bound only boundedness above has content.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, p. 16, Lemma 4.1 (proof pp. 17–19)

import Mathlib
import Definitions.Def_GivenDegreeSeq_MLE_BetaModel

namespace GivenDegreeSeq.MLE

/-- Lemma 4.1, p. 16. There is a function `c₄(c₁, c₂, c₃)`, independent of `n` and `d` and
bounded on every compact subset of its domain `(0, 1) × (0, 1) × (0, ∞)` (the reading of "a
constant that depends only on `c₁, c₂, c₃`" fixed at the start of §4, p. 16), such that for all
`c₁, c₂ ∈ (0, 1)` and `c₃ > 0`: if `d ∈ R̄` (the closure of the set of β-model expected degree
sequences), `c₂(n − 1) ≤ d_i ≤ c₁(n − 1)` for all `i`, and
`Σ_{j ∉ B} min{d_j, |B|} + |B|(|B| − 1) − Σ_{i ∈ B} d_i ≥ c₃ n²` for every `B` with
`|B| ≥ c₂² n`, then the ML equations (3) have a solution `β̂` with `|β̂|∞ ≤ c₄(c₁, c₂, c₃)`. -/
theorem lemma_4_1 :
    ∃ c₄ : ℝ → ℝ → ℝ → ℝ,
      (∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
        K ⊆ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioi (0 : ℝ) →
        BddAbove ((fun c : ℝ × ℝ × ℝ => c₄ c.1 c.2.1 c.2.2) '' K)) ∧
      ∀ c₁ c₂ c₃ : ℝ, c₁ ∈ Set.Ioo (0 : ℝ) 1 → c₂ ∈ Set.Ioo (0 : ℝ) 1 → 0 < c₃ →
        ∀ (n : ℕ) (d : Fin n → ℝ), d ∈ closure (R n) →
          (∀ i, c₂ * ((n : ℝ) - 1) ≤ d i ∧ d i ≤ c₁ * ((n : ℝ) - 1)) →
          (∀ B : Finset (Fin n), c₂ ^ 2 * (n : ℝ) ≤ (B.card : ℝ) →
            c₃ * (n : ℝ) ^ 2 ≤ slack d B) →
          ∃ βhat : Fin n → ℝ, GivenDegreeSeq.FixedPoint.MLEq d βhat ∧
            ‖βhat‖ ≤ c₄ c₁ c₂ c₃ := by sorry

end GivenDegreeSeq.MLE
