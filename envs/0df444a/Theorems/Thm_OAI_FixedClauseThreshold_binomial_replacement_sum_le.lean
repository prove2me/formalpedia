-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_binomial_replacement_sum_le
-- name    : OAI.FixedClauseThreshold.binomial_replacement_sum_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:54:44.778285+00:00
-- url     : https://prove2.me/theorems/b5513e07-db65-441d-8a62-ba938c1c3249
-- title:
--   Summed binomial bound for replacement differences of a monotone probability sequence
-- statement:
--   Let $0\le p\le1$, let $P:\mathbb N\to\mathbb R$ be nonincreasing with $0\le P(j)\le1$ for all $j$, let $g\ge1$ be an integer and let $M\in\mathbb N$. For $j,d\in\mathbb N$ define the *replacement difference*
--
--   $$
--   \Delta_j(d)=P(j-d)-P\big(j+(g-1)d\big),
--   $$
--
--   where $j-d$ is truncated at $0$. For $f:\mathbb N\to\mathbb R$ let $\mathbb E_{D\sim\operatorname{Bin}(j,p)}f(D)=\sum_{d=0}^{j}\binom jd p^d(1-p)^{j-d}f(d)$ denote the binomial expectation. Then
--
--   $$
--   \sum_{j=0}^{M}\ \mathbb E_{D\sim\operatorname{Bin}(j,p)}\Big[P(j-D)-P\big(j+(g-1)D\big)\Big]\ \le\ g\,M\,p .
--   $$
--
--   Inside the expectation $D\le j$, so no truncation actually occurs.
--
--   In the application, $P(j)$ is the probability that $j$ random clauses are satisfiable and $D$ counts the clauses that meet a distinguished variable; $\Delta_j(D)$ compares removing these $D$ clauses with replacing each of them by a block of $g$ clauses. The bound says that, summed over all clause counts up to $M$, these differences cost at most $gMp$, whatever the shape of $P$.
--
--   **Formalization Note** The binomial expectation is `binomialMean p j f`, defined by the recursion $B_0f=f(0)$, $B_{j+1}f=(1-p)B_jf+p\,B_j\big(f(\cdot+1)\big)$, which equals the displayed sum. $\Delta_j(d)$ is `replacementDifference P g j d`, written with natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Binomial.lean#L162-L177

import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial

open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable

theorem OAI.FixedClauseThreshold.binomial_replacement_sum_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P : ℕ → ℝ} (hP : Antitone P) (hP0 : ∀ j, 0 ≤ P j) (hP1 : ∀ j, P j ≤ 1)
    {g : ℕ} (hg : 1 ≤ g) (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), binomialMean p j (replacementDifference P g j) ≤
      (g : ℝ) * (M : ℝ) * p := by sorry
