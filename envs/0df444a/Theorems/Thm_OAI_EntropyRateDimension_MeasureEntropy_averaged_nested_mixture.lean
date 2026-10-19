-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_averaged_nested_mixture
-- name    : OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:12:44.163898+00:00
-- url     : https://prove2.me/theorems/c4ec0ba0-62ec-4b5f-8027-e4b742e5788f
-- title:
--   Refinement gains are concave under mixtures
-- statement:
--   For a probability measure $\mu$ on $\mathbb R$, a mesh $s>0$ and a shift $u$, the grid label is $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$, the grid entropy $H_{s,u}(\mu)=\sum_j-m_j\log m_j$ is the entropy of the masses $m_j=\mu\{\ell_{s,u}=j\}$, and the averaged grid entropy is $\bar H_s(\mu)=\int_0^1H_{s,u}(\mu)\,du$. A measure is compactly carried if it vanishes outside some interval $[-B,B]$.
--
--   Let $\mu=\sum_iw_i\nu_i$ be a finite mixture of compactly carried probability measures with $w_i\ge0$, and let $\mu$ be a probability measure. For $s>0$ and $N\ge1$,
--   $$
--   \sum_iw_i\bigl(\bar H_s(\nu_i)-\bar H_{Ns}(\nu_i)\bigr)\le\bar H_s(\mu)-\bar H_{Ns}(\mu).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L677-L703

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

theorem OAI.EntropyRateDimension.MeasureEntropy.averaged_nested_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∑ i, w i*(averaged (ν i) s-averaged (ν i) ((N : ℝ)*s))) ≤
      averaged μ s-averaged μ ((N : ℝ)*s) := by sorry
