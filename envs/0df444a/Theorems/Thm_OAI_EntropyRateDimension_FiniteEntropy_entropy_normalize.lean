-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_normalize
-- name    : OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T03:59:22.206983+00:00
-- url     : https://prove2.me/theorems/6171e8b1-40bc-4f3f-90c3-125813e5fa4c
-- title:
--   Entropy of unnormalized weights
-- statement:
--   Let $p$ be nonnegative weights on a finite set $s$, with total $P=\sum_{a\in s}p_a$. Then
--   $$
--   H(s,p)=-P\log P+P\cdot H\Bigl(s,\ \frac{p}{P}\Bigr),
--   $$
--   where $H(s,q)=\sum_{a\in s}-q_a\log q_a$.
--
--   When $P=0$ both sides vanish, with the convention $0\log0=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L116-L138

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.entropy_normalize {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * entropy s (fun a => p a / ∑ b ∈ s, p b) := by sorry
