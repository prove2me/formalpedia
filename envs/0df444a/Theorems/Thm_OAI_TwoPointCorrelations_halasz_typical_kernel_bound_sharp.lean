-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_halasz_typical_kernel_bound_sharp
-- name    : OAI.TwoPointCorrelations.halasz_typical_kernel_bound_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:03.489195+00:00
-- url     : https://prove2.me/theorems/43326f01-5122-4731-a5e6-658cc081afc3
-- title:
--   Under the two Halász inputs, the mean square of the typical dyadic polynomial off the small-value bands
-- statement:
--   Assume `HalaszPrimeSparseInput` and `HalaszHighPrimeInput` (the bundle's sparse large-values estimate for prime polynomials and the high-prime cosine lower bound). Then there is $C>0$ such that for all sufficiently large $N$: for every completely multiplicative $F$ on positive integers with $F(1)=1$ and $|F|\le1$; reals $2\le P\le Q$ with $\log P>1$, $\log Q\ge1$ and $\mathrm{res}(P,Q):=\exp((\frac16-\frac1{100})\log P-\frac13\log\log Q)\ge2$ (`mrtBaseResolution P Q (1/100)`); every $J\ge1$ such that for $k\in\{N,2N\}$, $200\log\log k+1\le\log\mathrm{lo}_J$ and $\mathrm{up}_J\le\exp(\sqrt{\log k})$ (the band endpoints `mrtBandLower P Q J`, `mrtBandUpper Q J`); every $X\in[N,N^3]$; every $M\ge0$ with $\mathbb D(F,n^{iu};X)^2\ge M$ for $|u|\le X$; every $k\in\{N,2N\}$ and $v\in[0,k/4]$:
--
--   $$\int_{(-v,v]\cap\mathcal B}\big|D_k(t)\big|^2dt\le C\Big(e^{-4M/5}+\frac{\log\log N}{(\log N)^{1/80}}\Big)\Big(\frac vk+1\Big),$$
--
--   where $D_k(t)=\sum_{k<n\le2k}\frac{G(n)}{n}n^{-it}$ (`mrtDyadicPolynomial`) for $G$ the restriction of $F$ to $n$ having a prime factor in each of the $J$ bands (`mrtTypicalCoefficient`), and $\mathcal B$ is the complement of the union of the small-frequency bands `mrtNoSmallBand (mrtLogFamilyBins …) (mrtLogFamilyPolynomial …) (mrtLogFamilyThreshold …) J` defined in the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.halasz_typical_kernel_bound_sharp`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open MeasureTheory
open scoped Classical

theorem halasz_typical_kernel_bound_sharp
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0< a → 0< b → F (a*b)=F a*F b) → OneBounded F →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 1 < Real.log P → 1 ≤ Real.log Q →
        2 ≤ mrtBaseResolution P Q (1/100) →
      ∀ J : ℕ, 1 ≤ J →
      (∀ k ∈ ({N,2*N}:Finset ℕ),
        200*Real.log (Real.log k)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        mrtBandUpper Q J ≤ Real.exp (Real.sqrt (Real.log k))) →
      ∀ X : ℕ, N ≤ X → X ≤ N^3 →
      ∀ M : ℝ, 0 ≤ M →
      (∀ u:ℝ, |u| ≤ X → M ≤ squaredDistance F (mrtArchimedeanTwist u) X) →
      ∀ k ∈ ({N,2*N}:Finset ℕ), ∀ v:ℝ, 0 ≤ v → v ≤ (k:ℝ)/4 →
      (∫ t in Set.Ioc (-v) v ∩ mrtNoSmallBand (mrtLogFamilyBins P Q (1/100))
          (mrtLogFamilyPolynomial
            (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F P Q (1/100))
          (mrtLogFamilyThreshold P Q (1/100)) J,
        ‖mrtDyadicPolynomial (mrtTypicalCoefficient (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) k t‖^2) ≤
        C*(Real.exp (-4*M/5)+
          Real.log (Real.log N)/(Real.log N)^(1/80:ℝ))*(v/k+1) := by
  sorry

end OAI.TwoPointCorrelations
