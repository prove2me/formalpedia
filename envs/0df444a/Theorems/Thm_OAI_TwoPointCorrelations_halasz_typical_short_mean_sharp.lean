-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_short_mean_sharp
-- name    : OAI.TwoPointCorrelations.halasz_typical_short_mean_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:13.975819+00:00
-- url     : https://prove2.me/theorems/6b82004c-dbac-4226-9080-64674cb146dc
-- title:
--   Under the two Halász inputs, typical numbers have small short exponential sums on average
-- statement:
--   Assume `HalaszPrimeSparseInput` and `HalaszHighPrimeInput`. Then there is $K>0$ such that for all sufficiently large $N$: for reals $2\le P\le Q$ with $\log P\ge2$, $\log Q\ge1$, $8192(\log\log Q+1)\le\frac1{100}\log P$ and $\mathrm{res}(P,Q)\ge2$ (`mrtBaseResolution P Q (1/100)`); every $J\ge1$ with, for $k\in\{N,2N\}$, $200\log\log k+1\le\log\mathrm{lo}_J$ and $\mathrm{up}_j\le\exp(\sqrt{\log k})$ for $j\le J$; every $X\in[N,N^3]$; every $H$ with $4\le H\le N$ and $2Q\le N$; every $W\ge1$ with $W^9\le\mathrm{res}(P,Q)$, $W^2\le P$, $W\le H$, $Q/H\le W^7$; every completely multiplicative $F$ on positive integers with $F(1)=1$, $|F|\le1$; and every $M\ge0$ with $\mathbb D(F,n^{iu};X)^2\ge M$ for $|u|\le X$:
--
--   $$\frac1{NH}\int_N^{2N}\Big|\sum_{x<n\le x+H}G(n)\Big|\,dx\le K\Big(e^{-2M/5}+\sqrt{\frac{\log\log N}{(\log N)^{1/80}}}+W^{-1}\Big),$$
--
--   where $G$ is the restriction of $F$ to integers with a prime factor in each of the $J$ bands (`mrtTypicalCoefficient`), and the inner sum is `shortExponentialSum G H 0 x` (over $\lfloor x\rfloor<n\le\lfloor x+H\rfloor$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_typical_short_mean_sharp`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open MeasureTheory

theorem halasz_typical_short_mean_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 → ∀ H : ℕ, 4 ≤ H → H ≤ N → 2*Q ≤ (N:ℝ) →
      ∀ W : ℝ, 1 ≤ W → W^9 ≤ mrtBaseResolution P Q (1/100) →
        W^2 ≤ P → W ≤ (H:ℝ) → Q/(H:ℝ) ≤ W^7 →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u : ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      (∫ x in (N:ℝ)..(2*N), ‖shortExponentialSum (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) H 0 x‖)/((N:ℝ)*H) ≤
      K*(Real.exp (-2*M/5)+Real.sqrt
        (Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))+W⁻¹) := by
  sorry

end OAI.TwoPointCorrelations
