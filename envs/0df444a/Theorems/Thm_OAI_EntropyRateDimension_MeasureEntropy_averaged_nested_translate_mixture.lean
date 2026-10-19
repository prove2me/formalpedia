-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_translate_mixture
-- name    : OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:13:47.895982+00:00
-- url     : https://prove2.me/theorems/a228127e-e86c-4727-9d54-0201a3c0a1ec
-- title:
--   Mixing translates does not decrease the refinement gain
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   Let $\mu$ be a compactly carried probability measure, $w_i\ge0$ weights summing to $1$, and $b_i$ real shifts. Let $\mu'=\sum_iw_i\,\mu(\cdot-b_i)$. For $s>0$ and $N\ge1$,
--   $$
--   \bar H_s(\mu)-\bar H_{Ns}(\mu)\le\bar H_s(\mu')-\bar H_{Ns}(\mu') .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L730-L753

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

theorem OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_translate_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (b : ι → ℝ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    averaged μ s-averaged μ ((N : ℝ)*s) ≤
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) s-
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) ((N : ℝ)*s) := by sorry
