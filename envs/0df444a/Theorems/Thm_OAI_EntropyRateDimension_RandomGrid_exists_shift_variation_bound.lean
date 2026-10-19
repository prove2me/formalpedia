-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_exists_shift_variation_bound
-- name    : OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:28:21.491166+00:00
-- url     : https://prove2.me/theorems/5d55fa6e-4259-4600-8a2b-b17d347c3e6f
-- title:
--   A good grid shift for many hit indicators
-- statement:
--   The hit indicator $\mathrm{hit}(c,r,u)$ is $1$ if $u$ lies within circle distance $r$ of $c$, and $0$ otherwise.
--
--   Let $p\ge0$ be weights on a finite set $s$, and $v,m:s\to\mathbb R^k$, $\delta>0$. There is a shift $u\in\mathbb R/\mathbb Z$ with
--   $$
--   \sum_xp(x)\sum_{i,j}\mathrm{hit}\Bigl(-\frac{m_j(x)}\delta,\ \frac{4k|v_i(x)-m_i(x)|}\delta,\ u\Bigr)\le\frac{8k^2}\delta\sum_xp(x)\sum_i|v_i(x)-m_i(x)| .
--   $$
--
--   A random shift hits a circle arc of radius $r$ with probability at most $2r$, so some shift does no worse than average.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean#L282-L311

import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.RandomGrid
universe uα
open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] unitCircleProbability

theorem OAI.EntropyRateDimension.RandomGrid.exists_shift_variation_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (v m : α → Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u) ≤
      (8*k^2/δ)*(∑ x ∈ s, p x * ∑ i, |v x i-m x i|) := by sorry
