-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_entropy_map_injective
-- name    : OAI.EntropyRateDimension.FiniteDistribution.entropy_map_injective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:08:11.993679+00:00
-- url     : https://prove2.me/theorems/372cd530-a7ef-4268-a7f5-efd15925a1ac
-- title:
--   Injective relabelling preserves entropy
-- statement:
--   Let $p$ be a finitely supported probability distribution on a type $\alpha$ and $f:\alpha\to\beta$ injective. Then the pushforward has the same entropy:
--   $$
--   H(f_*p)=H(p),\qquad H(p)=\sum_a-p(a)\log p(a).
--   $$
--
--   For example, translating a distribution on $\mathbb Z$ does not change its entropy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteDistribution.lean#L207-L219

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem OAI.EntropyRateDimension.FiniteDistribution.entropy_map_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).entropy=p.entropy := by sorry
