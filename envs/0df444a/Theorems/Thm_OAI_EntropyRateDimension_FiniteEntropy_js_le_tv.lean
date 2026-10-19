-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_js_le_tv
-- name    : OAI.EntropyRateDimension.FiniteEntropy.js_le_tv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:07:41.39506+00:00
-- url     : https://prove2.me/theorems/55b4e00b-8f71-47b0-8b73-6e23f9cd576a
-- title:
--   Jensen–Shannon divergence is at most total variation times log 2
-- statement:
--   Let $p,q$ be probability weights on a finite set $s$. Define the Jensen–Shannon divergence and total variation by
--   $$
--   \mathrm{JS}(p,q)=H\Bigl(\frac{p+q}2\Bigr)-\frac{H(p)+H(q)}2,\qquad\mathrm{TV}(p,q)=\frac12\sum_{a\in s}|p_a-q_a| .
--   $$
--   Then $\mathrm{JS}(p,q)\le\mathrm{TV}(p,q)\log2$.
--
--   Entropies are in natural units, so $\log2$ is one bit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean#L1096-L1122

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FiniteEntropy.js_le_tv {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    js s p q ≤ totalVariation s p q*Real.log 2 := by sorry
