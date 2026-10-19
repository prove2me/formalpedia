-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteDistribution_js_le_map_add
-- name    : OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:16:42.837284+00:00
-- url     : https://prove2.me/theorems/af59c67f-e7bc-474c-94bf-6528f2e76e71
-- title:
--   Jensen–Shannon divergence under a map, with an entropy correction
-- statement:
--   Let $p,q$ be finitely supported probability distributions on $\alpha$ and $f:\alpha\to\beta$ any map. With $\mathrm{JS}(p,q)=H(\frac{p+q}2)-\frac{H(p)+H(q)}2$,
--   $$
--   \mathrm{JS}(p,q)\le\mathrm{JS}(f_*p,f_*q)+H\Bigl(\frac{p+q}2\Bigr)-H\Bigl(f_*\frac{p+q}2\Bigr).
--   $$
--
--   The correction term is the entropy of the even mixture lost by applying $f$, which vanishes when $f$ is injective on the supports.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/RandomGrid.lean#L21-L33

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteDistribution
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem OAI.EntropyRateDimension.FiniteDistribution.js_le_map_add {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    p.js q ≤ (p.map f).js (q.map f)+(p.mix q).entropy-((p.mix q).map f).entropy := by sorry
