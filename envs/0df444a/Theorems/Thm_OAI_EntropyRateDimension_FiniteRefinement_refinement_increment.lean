-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_refinement_increment
-- name    : OAI.EntropyRateDimension.FiniteRefinement.refinement_increment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:30:11.120988+00:00
-- url     : https://prove2.me/theorems/e087dc93-5937-4529-9b1d-91ab610c320a
-- title:
--   Chain rule for refining a partition by a grid
-- statement:
--   Let $x_1,\dots,x_k$ be i.i.d. with law $p$ on a finite set, $v$ real values, and $g$ a partition label with values in lists of integers. Refine $g$ by prepending the grid cell, $g'(a)=\mathrm{cell}_{\delta,u}(v(a))::g(a)$, and let $Y=\sum_iv(x_i)$. Then
--   $$
--   H\bigl((g'(x_i))_i\mid Y\bigr)=H\bigl((g(x_i))_i\mid Y\bigr)+H\Bigl(\bigl(\mathrm{cell}_{\delta,u}(v(x_i))\bigr)_i\ \Big|\ Y,(g(x_i))_i\Bigr).
--   $$
--
--   So the cost of a refinement is the entropy of the new cells given the sum and the old tags.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean#L240-L270

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteRefinement
universe uα uβ uγ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem OAI.EntropyRateDimension.FiniteRefinement.refinement_increment (p : α → ℝ) (v : α → ℝ) (g : α → List ℤ)
    (hp : ∀ a, 0 ≤ p a) (k : ℕ) (δ : ℝ) (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)) :: g (x i)) (fun x => ∑ i, v (x i)) =
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) (fun x => ∑ i, v (x i)) +
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) := by sorry
