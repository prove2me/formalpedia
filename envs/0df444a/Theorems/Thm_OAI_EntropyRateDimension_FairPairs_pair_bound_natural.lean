-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FairPairs_pair_bound_natural
-- name    : OAI.EntropyRateDimension.FairPairs.pair_bound_natural
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:32:20.580375+00:00
-- url     : https://prove2.me/theorems/16b7163a-86fa-43f9-b799-420792734934
-- title:
--   Entropy below scale is bounded by sumset size and band capacities
-- statement:
--   Let $\nu$ be a finite law on $\mathbb R$, $k\ge1$ and $\rho>0$. Let $H(\nu)$ be its entropy and $H_\rho(\nu)$ the entropy of $\lfloor x/\rho\rfloor$, both in natural units. Let $A_k$ be the set of sums of $k$ support points. Then
--   $$
--   k\bigl(H(\nu)-H_\rho(\nu)\bigr)\le\log|A_k|+60000\,k^4\log2\sum_{\ell:\ 2^{-\ell}\le2\rho}\mathrm{cap}(\nu,\ell),
--   $$
--   where $\ell$ ranges over band indices of pairs of support points.
--
--   If the entropy of $\nu$ below scale $\rho$ is large while the sumset stays small, the law must contain many separated pairs at distances up to about $\rho$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/SumsetBound.lean#L269-L321

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

theorem OAI.EntropyRateDimension.FairPairs.pair_bound_natural (ν : Law) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    k * (entropy ν.support ν.prob - observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋)) ≤
      Real.log (ν.sumset k).card + 60000*k^4*Real.log 2 *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ := by sorry
