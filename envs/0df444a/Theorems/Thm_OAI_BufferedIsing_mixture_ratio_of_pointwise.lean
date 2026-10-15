-- Prove2me | Theorems.Thm_OAI_BufferedIsing_mixture_ratio_of_pointwise
-- name    : OAI.BufferedIsing.mixture_ratio_of_pointwise
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:16:23.142717+00:00
-- url     : https://prove2.me/theorems/ff0b64cc-2fd0-4273-95ec-1fcd355804d2
-- title:
--   Pointwise ratio bounds survive arbitrary probability mixtures
-- statement:
--   Let $B$ be a finite set and let $p:B\to\mathbb{R}$ be strictly positive, $p(b)>0$ for all $b\in B$. Suppose that real constants $L$ and $U$ control all pairwise ratios of $p$, that is, $L\le p(b)/p(b')\le U$ for all $b,b'\in B$. Let $\mu,\nu:B\to\mathbb{R}$ be probability weights: $\mu(b)\ge0$ and $\nu(b)\ge0$ for all $b$, and $\sum_{b\in B}\mu(b)=\sum_{b\in B}\nu(b)=1$. Then the $\mu$-average and the $\nu$-average of $p$ obey the same ratio bounds:
--
--   $$
--   L\;\le\;\frac{\sum_{b\in B}\mu(b)\,p(b)}{\sum_{b\in B}\nu(b)\,p(b)}\;\le\;U .
--   $$
--
--   The point is that no constant is lost when one passes from pointwise comparisons to arbitrary mixtures on both sides. In the buffered Ising comparison, $p(b)$ is the conditional probability of a fixed event on one block given a prescription $b$ on another block, and the lemma upgrades a uniform bound on ratios of such conditional probabilities to the same bound for ratios of arbitrary mixtures of them.
--
--   **Formalization Note** $B$ is any type with a `Fintype` instance. It is automatically nonempty because $\sum_b\nu(b)=1$, so the denominator is a genuine positive number and Lean's convention for division by zero plays no role.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Marginals.lean#L235-L271

import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals

open OAI OAI.BufferedIsing
open scoped BigOperators Classical

theorem OAI.BufferedIsing.mixture_ratio_of_pointwise {B : Type*} [Fintype B]
    (p : B → ℝ) (hp : ∀ b, 0 < p b) (L U : ℝ)
    (hbound : ∀ b b', L ≤ p b / p b' ∧ p b / p b' ≤ U)
    (μ ν : B → ℝ) (hμ : ∀ b, 0 ≤ μ b) (hν : ∀ b, 0 ≤ ν b)
    (hμsum : ∑ b, μ b = 1) (hνsum : ∑ b, ν b = 1) :
    L ≤ (∑ b, μ b * p b) / (∑ b, ν b * p b) ∧
      (∑ b, μ b * p b) / (∑ b, ν b * p b) ≤ U := by sorry
