-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_grid_le_grid_add_log
-- name    : OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:10:54.138257+00:00
-- url     : https://prove2.me/theorems/f94afe46-f827-4861-a897-7df3da7ed571
-- title:
--   Comparing grid entropies at two scales
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   For a compactly carried probability measure $\mu$, meshes $s,t>0$ and shifts $u,v$,
--   $$
--   H_{s,u}(\mu)\le H_{t,v}(\mu)+\log\bigl(\lceil t/s\rceil+1\bigr).
--   $$
--
--   The finer grid carries at most $\log(\lceil t/s\rceil+1)$ more information than the coarser one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L486-L504

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uι uα uβ uγ uδ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.MeasureEntropy.grid_le_grid_add_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (⌈t/s⌉+1 : ℝ) := by sorry
