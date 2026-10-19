-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_CompactlyCarried_mixture
-- name    : OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:13:18.821765+00:00
-- url     : https://prove2.me/theorems/00cfcb53-55c4-4a0d-addf-d2868f4b849e
-- title:
--   Finite mixtures of compactly carried measures
-- statement:
--   Let $\nu_i$, for $i$ in a finite index set, be measures on $\mathbb R$, each vanishing outside some bounded interval, and let $w_i$ be real numbers. Then the mixture with coefficients $\max(w_i,0)$ is again compactly carried: there is $B\ge0$ with
--   $$
--   \Bigl(\sum_i\max(w_i,0)\,\nu_i\Bigr)\bigl(\mathbb R\setminus[-B,B]\bigr)=0 .
--   $$
--
--   Negative coefficients are truncated to $0$, as in the conversion of reals to nonnegative extended reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L705-L719

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

theorem OAI.EntropyRateDimension.MeasureEntropy.CompactlyCarried.mixture {ι : Type uι} [Fintype ι]
    (ν : ι → Measure ℝ) (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) :
    CompactlyCarried (∑ i, ENNReal.ofReal (w i) • ν i) := by sorry
