-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_MeasureEntropy_mass_fairShift
-- name    : OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:14:31.969312+00:00
-- url     : https://prove2.me/theorems/9fb3af49-4d88-45a9-9e27-1f423192874b
-- title:
--   Grid masses of a fair shift
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$, $s>0$, and let $\mu'=\frac12\bigl(\mu+\mu(\cdot-s)\bigr)$ be the average of $\mu$ and its translate by one mesh. For the grid label $\ell_{s,u}(x)=\lfloor x/s+u\rfloor$ and every $j\in\mathbb Z$,
--   $$
--   \mu'\{\ell_{s,u}=j\}=\frac{\mu\{\ell_{s,u}=j\}+\mu\{\ell_{s,u}=j-1\}}2 .
--   $$
--
--   So the grid law of the fair shift is the even mixture of the grid law of $\mu$ and its translate by one cell.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/MeasureEntropy.lean#L800-L821

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

theorem OAI.EntropyRateDimension.MeasureEntropy.mass_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by sorry
