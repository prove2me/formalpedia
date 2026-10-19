-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FiniteRefinement_exists_entropy_step
-- name    : OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:29:34.47108+00:00
-- url     : https://prove2.me/theorems/bd5ea55c-1f26-4f14-9a37-042418596e8c
-- title:
--   One grid refinement step costs little conditional entropy
-- statement:
--   For a mesh $\delta>0$ and a point $u$ of the circle $\mathbb R/\mathbb Z$ with representative $\tilde u\in[0,1)$, the cell of $x$ is $\mathrm{cell}_{\delta,u}(x)=\lfloor x/\delta+\tilde u\rfloor$. Conditional entropy is $H(f\mid g)=H(f,g)-H(g)$ in natural units.
--
--   Let $p>0$ be a probability on a finite set, $v$ real values and $g$ a partition whose cells have diameter at most $4\delta$ in $v$. Draw $x_1,\dots,x_k$ i.i.d. from $p$ with $k\ge1$. There is a shift $u$ with
--   $$
--   H\Bigl(\bigl(\mathrm{cell}_{\delta,u}(v(x_i))\bigr)_i\ \Big|\ \sum_iv(x_i),\ (g(x_i))_i\Bigr)\le\frac{88k^4}\delta\log2\sum_ap(a)\,|v(a)-\bar v(g(a))| ,
--   $$
--   where $\bar v$ is the cell mean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FiniteRefinement.lean#L219-L238

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

theorem OAI.EntropyRateDimension.FiniteRefinement.exists_entropy_step (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) :
    ∃ u : AddCircle (1 : ℝ),
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    (88*k^4/δ)*(∑ a, p a*|v a-cellMean p v g (g a)|)*Real.log 2 := by sorry
