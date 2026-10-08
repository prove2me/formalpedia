-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_major_arc_corrected_typical_mean
-- name    : OAI.TwoPointCorrelations.major_arc_corrected_typical_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:10.543869+00:00
-- url     : https://prove2.me/theorems/60f5232a-aaa8-4ec2-97c8-de5d254f2c21
-- title:
--   Under the two Halász inputs, the short exponential integral of typical numbers near a rational with small denominator
-- statement:
--   Assume `HalaszPrimeSparseInput` and `HalaszHighPrimeInput`. Then there are $C>0$ and $N_0\in\mathbb N$ such that for all naturals $X,V,H,K,H_0$ with $X\ge2$, $\log X\ge1$, $H\le V$, $K\ge\max(N_0,1,\sqrt X)$; reals $2\le P\le Q$ with $\log P\ge2$, $\log Q\ge1$, $8192(\log\log Q+1)\le\frac1{100}\log P$, `mrtBaseResolution P Q (1/100)` $\ge2$ and $2Q\le K$; every $J\ge1$ such that for all $n\in[K,2X]$, $200\log\log n+1\le\log\mathrm{lo}_J$ and $\mathrm{up}_j\le\exp(\sqrt{\log n})$ for $j\le J$ (band endpoints `mrtBandLower`, `mrtBandUpper`); every $W\in[2,K]$ with $W^9\le$ `mrtBaseResolution P Q (1/100)`, $W^5\le P$, $W^{250}\le H$, and the compatibility conditions on $V/d$, $H/d$, $q$, $k/b$ stated in the Lean for $d\le\lfloor W^5\rfloor$ (`mrtCorrectionCutoff W`); every $q\ge1$ with $q\le W$ and $q\le$ `mrtModulusCutoff X H₀` $=\min((\log X)^{1/125},(\log H_0)^5)$; every multiplicative $F$ with $F(1)=1$, $|F|\le1$; every $M\ge0$ with `MRTDistanceLowerBound F X H₀ M` (for every $q'\le$ `mrtModulusCutoff X H₀`, character $\chi$ mod $q'$ and $|t|\le X$, $\mathbb D(F,\chi n^{it};X)^2\ge M$); and every $r\in\mathbb Z$, $\beta$ with $|\beta|H\le1$:
--
--   $$\int_0^V\Big|\sum_{y<n\le y+H}G(n)e\big(n(\tfrac rq+\beta)\big)\Big|dy\le c_*VH\Big(4(1+4\pi)\Big(4C\sqrt W(1+\log W)\Big(e^{-2M/5}+\sqrt{\tfrac{\log\log X}{(\log X)^{1/80}}}+W^{-1}\Big)+\tfrac3W\Big)+5W^{-5/4}\Big),$$
--
--   where $G$ is the restriction of $F$ to integers with a prime factor in each of the $J$ bands (`mrtTypicalCoefficient`), the left side is `shortExponentialIntegral G V H (r/q+β)`, $e(x)=e^{2\pi ix}$, and $c_*$ = `mrtCorrectionBound` is an explicit constant of the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.major_arc_corrected_typical_mean`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem major_arc_corrected_typical_mean
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → H ≤ V → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 2 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^5 ≤ P →
      W^250 ≤ (H:ℝ) →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W →
        V/d+1 ≤ 2*X ∧ (2*(K:ℝ)+1)/(V/d+1:ℕ) ≤ (W^4)⁻¹) →
      ∀ q : ℕ, 0 < q → (q:ℝ) ≤ W → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d : ℕ, 0 < d → d ≤ mrtCorrectionCutoff W → q ≤ V/d+1 ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ H/d+1 → ((H/d+1:ℕ):ℝ)/W^2 ≤ k →
          ∀ b ∈ q.divisors, 4 ≤ k/b+1 ∧ k/b+1 ≤ K ∧
            W ≤ (k/b+1:ℕ) ∧ Q/(k/b+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → Multiplicative F → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ, ∀ β : ℝ,
      |β| *(H:ℝ) ≤ 1 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q+β) ≤
      mrtCorrectionBound*(V:ℝ)*H*
        (4*(1+4*Real.pi)*(4*C*(Real.sqrt W*(1+Real.log W))*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+3/W)+
          5*W^(-5/4:ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
