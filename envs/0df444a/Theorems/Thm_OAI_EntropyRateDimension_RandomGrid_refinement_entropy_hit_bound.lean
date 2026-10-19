-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_RandomGrid_refinement_entropy_hit_bound
-- name    : OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:27:52.23429+00:00
-- url     : https://prove2.me/theorems/00c1fdec-cd62-4fd0-8316-65bf9e7c26a9
-- title:
--   Refinement entropy bounded by grid hits
-- statement:
--   For a mesh $\delta>0$ and a point $u$ of the circle $\mathbb R/\mathbb Z$ with representative $\tilde u\in[0,1)$, the cell of $x$ is $\mathrm{cell}_{\delta,u}(x)=\lfloor x/\delta+\tilde u\rfloor$. Conditional entropy is $H(f\mid g)=H(f,g)-H(g)$ in natural units. The hit indicator $\mathrm{hit}(c,r,u)$ is $1$ if $u$ lies within circle distance $r$ of $c$, and $0$ otherwise.
--
--   Let $p$, $v$, $m$ be as before, with $|v_i(x)-m_i|\le4\delta$, and assume the deviation events $\{|v_i-m_i|\ge a/(4k)\}$ are pairwise independent for every threshold $a$. Then
--   $$
--   H\Bigl(\bigl(\mathrm{cell}_{\delta,u}(v_i)\bigr)_i\ \Big|\ \sum_iv_i\Bigr)\le11k\log2\sum_xp(x)\sum_{i,j}\mathrm{hit}\Bigl(-\frac{m_j}\delta,\ \frac{4k|v_i(x)-m_i|}\delta,\ u\Bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/GridCoupling.lean#L235-L280

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

theorem OAI.EntropyRateDimension.RandomGrid.refinement_entropy_hit_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (v : α → Fin k → ℝ) (m : Fin k → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ)
    (hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| ∧ a/(4*k) ≤ |v x j-m j| then p x else 0) =
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0) *
      (∑ x ∈ s, if a/(4*k) ≤ |v x j-m j| then p x else 0)) :
    FiniteEntropy.conditionalEntropy s p (fun x i => cell δ u (v x i)) (fun x => ∑ i, v x i) ≤
      11*k*(∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u)*Real.log 2 := by sorry
