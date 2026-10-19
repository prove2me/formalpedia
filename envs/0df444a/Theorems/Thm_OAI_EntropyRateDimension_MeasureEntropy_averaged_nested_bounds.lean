-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_bounds
-- name    : OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:12:07.36451+00:00
-- url     : https://prove2.me/theorems/f893d250-63ac-4839-994e-368314bce87b
-- title:
--   Averaged entropy gained by refining a grid N times
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   For a compactly carried probability measure $\mu$, a mesh $s>0$ and an integer $N\ge1$,
--   $$
--   0\le\bar H_s(\mu)-\bar H_{Ns}(\mu)\le\log N .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L581-L598

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

theorem OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    0 ≤ averaged μ s-averaged μ ((N : ℝ)*s) ∧
      averaged μ s-averaged μ ((N : ℝ)*s) ≤ Real.log N := by sorry
