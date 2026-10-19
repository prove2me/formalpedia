-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FairPairs_sum_refinementCost_le
-- name    : OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:31:48.589358+00:00
-- url     : https://prove2.me/theorems/a50fbb75-057b-4422-ba1c-1cb7a56da42d
-- title:
--   Total cost of geometric refinements is bounded by band capacities
-- statement:
--   Let $\nu$ be a finite law on $\mathbb R$ with band capacities $\mathrm{cap}(\nu,\ell)$, and for a scale $R$ let the refinement cost be
--   $$
--   \mathrm{RC}_k(R)=\frac{352k^4}R\log2\sum_{\ell:\ 2^{-\ell}\le R}2^{1-\ell}\,\mathrm{cap}(\nu,\ell),
--   $$
--   with $\ell$ over band indices of the support. Then for $\rho>0$ and $J\ge0$,
--   $$
--   \sum_{h<J}\mathrm{RC}_k(\rho/4^h)\le60000\,k^4\log2\sum_{\ell:\ 2^{-\ell}\le2\rho}\mathrm{cap}(\nu,\ell) .
--   $$
--
--   Each band is charged only at the few scales just above its distance, so the geometric sum over scales collapses to a constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean#L203-L247

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uβ
open scoped BigOperators ENNReal
open MeasureTheory
open FiniteEntropy

theorem OAI.EntropyRateDimension.FairPairs.sum_refinementCost_le (ν : Law) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) ≤
      60000*k^4*Real.log 2 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ),
        capacity ν ℓ := by sorry
