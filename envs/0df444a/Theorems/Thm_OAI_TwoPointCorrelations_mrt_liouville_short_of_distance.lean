-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_liouville_short_of_distance
-- name    : OAI.TwoPointCorrelations.mrt_liouville_short_of_distance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:14:19.300506+00:00
-- url     : https://prove2.me/theorems/df202608-0f01-4cc5-9ff8-6d325c52270b
-- title:
--   The Matomäki–Radziwiłł bound for the Liouville function from the general input and a distance lower bound
-- statement:
--   Assume `MRTShortExponentialInput` (the bundle's short exponential-sum bound for multiplicative functions in terms of a distance lower bound). Suppose there is $K\ge0$ such that for all sufficiently large $X$, every $q$ with $1\le q\le(\log X)^{1/125}$, every Dirichlet character $\chi$ modulo $q$ and every $|t|\le X$,
--
--   $$\tfrac1{10}\log\log X-K\le\mathbb D(\lambda,\chi n^{it};X)^2=\sum_{p\le X}\frac{1-\operatorname{Re}\lambda(p)\overline{\chi(p)p^{it}}}{p}.$$
--
--   Then `MRTLiouvilleShortInput` holds: there is $C>0$ with `shortExponentialIntegral liouville X H α` $\le C\,H\,X\,$`mrtShortError X H` for all $10\le H\le X$ and real $\alpha$, where `mrtShortError X H` $=\frac{\log\log H}{\log H}+(\log X)^{-1/700}$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_liouville_short_of_distance`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem mrt_liouville_short_of_distance (hMRT : MRTShortExponentialInput)
    (hdistance : ∃ K : ℝ, 0≤ K ∧ ∀ᶠ X : ℕ in atTop,
      ∀ q : ℕ, 0< q → (q:ℝ)≤(Real.log (X:ℝ))^(1/125:ℝ) →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, |t|≤ X →
        (1/10:ℝ)*Real.log (Real.log (X:ℝ))-K ≤
          squaredDistance liouville (characterTwist χ t) X) :
    MRTLiouvilleShortInput := by
  sorry

end OAI.TwoPointCorrelations
