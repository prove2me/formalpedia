-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card
-- name    : OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T03:58:55.127206+00:00
-- url     : https://prove2.me/theorems/c7899b1e-d265-42b5-99f2-a2a1af495930
-- title:
--   Entropy is at most the log of the support size
-- statement:
--   Let $s$ be a finite set and $p$ nonnegative weights on $s$ with $\sum_{a\in s}p_a=1$. Then
--   $$
--   H(s,p)=\sum_{a\in s}-p_a\log p_a\ \le\ \log|s| .
--   $$
--
--   Logarithms are natural. The bound is attained by the uniform distribution on $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L80-L102

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.entropy_le_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    entropy s p ≤ Real.log s.card := by sorry
