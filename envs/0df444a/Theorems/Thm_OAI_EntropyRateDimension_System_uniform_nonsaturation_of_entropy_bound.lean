-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_System_uniform_nonsaturation_of_entropy_bound
-- name    : OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:16:14.45299+00:00
-- url     : https://prove2.me/theorems/9654860a-e513-4319-bfce-6cb50dff6e73
-- title:
--   Sub-maximal entropy growth forces a uniform scale deficit
-- statement:
--   Let $\mu$ be the self-similar probability measure of a system $f_i(x)=r_ix+b_i$ with weights $w_i$. For $s>0$ let $\bar H_s(\mu)$ be the averaged grid entropy at mesh $s$, and let the scale deficit be
--   $$
--   \mathrm{def}(v)=\log2-\bigl(\bar H_v(\mu)-\bar H_{2v}(\mu)\bigr).
--   $$
--   Suppose $\bar H_s(\mu)\le d\log(1/s)+C$ for all $s\in(0,1)$, with $d<1$. Then there is $\delta>0$ with $\mathrm{def}(v)\ge\delta$ for every $v>0$.
--
--   So the entropy never gains almost a full bit when the scale halves, uniformly over all scales.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/EntropyBounds.lean#L172-L208

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem OAI.EntropyRateDimension.System.uniform_nonsaturation_of_entropy_bound (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) {d C : ℝ} (hd : d < 1)
    (hu : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → δ ≤ deficit μ v := by sorry
