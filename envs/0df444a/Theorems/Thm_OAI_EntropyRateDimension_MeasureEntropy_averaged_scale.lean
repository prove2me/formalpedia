-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_scale
-- name    : OAI.EntropyRateDimension.MeasureEntropy.averaged_scale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:09:51.72686+00:00
-- url     : https://prove2.me/theorems/7ea1b46c-49b4-448c-bc15-e02f070e3a83
-- title:
--   Scaling a measure rescales its averaged grid entropy
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   For a compactly carried probability measure $\mu$, a mesh $s>0$ and $a\ne0$,
--   $$
--   \bar H_s\bigl((x\mapsto ax)_*\mu\bigr)=\bar H_{s/|a|}(\mu) .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L398-L413

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

theorem OAI.EntropyRateDimension.MeasureEntropy.averaged_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/|a|) := by sorry
