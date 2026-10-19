-- Prove2me | Theorems.Thm_OAI_EntropyRateDimension_FairPairs_coupling_distance_le
-- name    : OAI.EntropyRateDimension.FairPairs.coupling_distance_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:21:24.687301+00:00
-- url     : https://prove2.me/theorems/dcecb17f-f50d-4865-bfb3-abb74030167c
-- title:
--   Transport cost of a symmetric coupling bounded by band capacities
-- statement:
--   Let $\nu$ be a finite law on $\mathbb R$ and $\pi(x,y)\ge0$ a symmetric function on its support with row sums $\sum_y\pi(x,y)\le\nu(x)$, vanishing when $|y-x|>R$. For $\ell\in\mathbb Z$ let $\mathrm{cap}(\nu,\ell)$ be the largest total weight of a feasible pairing at distances in $[2^{-\ell},2^{1-\ell})$. Then
--   $$
--   \sum_{x,y}\pi(x,y)\,|y-x|\le\sum_{\ell:\ 2^{-\ell}\le R}2^{1-\ell}\,\mathrm{cap}(\nu,\ell),
--   $$
--   where $\ell$ ranges over band indices of pairs of support points.
--
--   Thus a coupling that moves mass over long distances requires large capacities in the corresponding bands.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/SelfSimilar/FairPairs.lean#L333-L388

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FairPairs
universe uι uα uβ
open scoped BigOperators ENNReal
open MeasureTheory

theorem OAI.EntropyRateDimension.FairPairs.coupling_distance_le {ν : Law} (π : ℝ → ℝ → ℝ) (R : ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x)
    (hdiam : ∀ x ∈ ν.support, ∀ y ∈ ν.support, R < |y - x| → π x y = 0) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support, π x y * |y - x|) ≤
      ∑ ℓ ∈ ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
        (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R), (2 : ℝ) ^ (1 - ℓ) * capacity ν ℓ := by sorry
