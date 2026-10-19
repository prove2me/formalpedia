-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_integral_gridInformation
-- name    : OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:20:25.30264+00:00
-- url     : https://prove2.me/theorems/5de265c7-23cc-4fc8-b192-317e4de59ef0
-- title:
--   Average grid information of a fair shift
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)$ is the entropy of the masses $\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. For a translation $v$, the fair shift is $\mu^v=\frac12\bigl(\mu+\mu(\cdot-v)\bigr)$, and the grid information is
--   $$
--   I_{s,u}(v)=H_{s,u}(\mu^v)-\frac{H_{s,u}(\mu)+H_{s,u}(\mu(\cdot-v))}2\ \ge0 .
--   $$
--
--   For a compactly carried probability measure $\mu$, any $v$ and $s>0$,
--   $$
--   \int_0^1I_{s,u}(v)\,du=\bar H_s(\mu^v)-\bar H_s(\mu).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/TranslationGain.lean#L175-L188

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable

theorem OAI.EntropyRateDimension.MeasureEntropy.integral_gridInformation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u in (0 : ℝ)..1, gridInformation μ v s u) = averaged (fairShift μ v) s-averaged μ s := by sorry
