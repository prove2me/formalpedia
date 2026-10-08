-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_major_arc_typical_rational_global
-- name    : OAI.TwoPointCorrelations.major_arc_typical_rational_global
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:12.996339+00:00
-- url     : https://prove2.me/theorems/78c87caa-c317-4ede-b3df-b525cf6112d5
-- title:
--   Under the two Halász inputs, the short exponential integral of typical numbers at a rational r/q
-- statement:
--   Assume `HalaszPrimeSparseInput` and `HalaszHighPrimeInput`. Then there are $C>0$ and $N_0$ such that for all naturals $X,V,H,K,H_0$ with $X\ge2$, $\log X\ge1$, $V\le2X$, $K\ge\max(N_0,1,\sqrt X)$; reals $2\le P\le Q$ with $\log P\ge2$, $\log Q\ge1$, $8192(\log\log Q+1)\le\frac1{100}\log P$, `mrtBaseResolution P Q (1/100)` $\ge2$, $2Q\le K$; every $J\ge1$ with the band conditions for $n\in[K,2X]$ as in the Lean; every $W\in[1,K]$ with $W^9\le$ `mrtBaseResolution P Q (1/100)` and $W^2\le P$; every $q$ with $1\le q\le\min(V,H)$, $q\le$ `mrtModulusCutoff X H₀`, every divisor $d$ of $q$ free of the band primes (`mrtPrimeAvoids`), and $4\le\lfloor H/d\rfloor+1\le K$, $W\le\lfloor H/d\rfloor+1$, $Q/(\lfloor H/d\rfloor+1)\le W^7$ for $d\mid q$; every completely multiplicative $F$ on positive integers with $F(1)=1$, $|F|\le1$; every $M\ge0$ with `MRTDistanceLowerBound F X H₀ M`; and every $r\in\mathbb Z$:
--
--   $$\int_0^V\Big|\sum_{y<n\le y+H}G(n)e(nr/q)\Big|dy\le\sqrt q\Big((1+\log q)\Big(4CVH\Big(e^{-2M/5}+\sqrt{\tfrac{\log\log X}{(\log X)^{1/80}}}+W^{-1}\Big)+2q(2K+1)H\Big)+qV\Big),$$
--
--   with $G$ = `mrtTypicalCoefficient (Icc 1 J) (band primes) F` and the left side `shortExponentialIntegral G V H (r/q)`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.major_arc_typical_rational_global`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset

theorem major_arc_typical_rational_global
    (hprime : HalaszPrimeSparseInput) (hhigh : HalaszHighPrimeInput) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ X V H K H₀ : ℕ,
      2 ≤ X → 1 ≤ Real.log (X:ℝ) → V ≤ 2*X → N₀ ≤ K → 1 ≤ K →
      Real.sqrt (X:ℝ) ≤ K →
      ∀ P Q : ℝ, 2 ≤ P → P ≤ Q → 2 ≤ Real.log P → 1 ≤ Real.log Q →
      8192*(Real.log (Real.log Q)+1) ≤ (1/100:ℝ)*Real.log P →
      2 ≤ mrtBaseResolution P Q (1/100) → 2*Q ≤ K →
      ∀ J : ℕ, 1 ≤ J →
      (∀ n : ℕ, K ≤ n → n ≤ 2*X →
        200*Real.log (Real.log n)+1 ≤ Real.log (mrtBandLower P Q J) ∧
        ∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤ Real.exp (Real.sqrt (Real.log n))) →
      ∀ W : ℝ, 1 ≤ W → W ≤ K → W^9 ≤ mrtBaseResolution P Q (1/100) → W^2 ≤ P →
      ∀ q : ℕ, 0 < q → q ≤ V → q ≤ H → (q:ℝ) ≤ mrtModulusCutoff X H₀ →
      (∀ d ∈ q.divisors, mrtPrimeAvoids ((Icc 1 J).biUnion
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))) d) →
      (∀ d ∈ q.divisors, 4 ≤ H/d+1 ∧ H/d+1 ≤ K ∧
        W ≤ (H/d+1:ℕ) ∧ Q/(H/d+1:ℕ) ≤ W^7) →
      ∀ F : ℕ → ℂ, F 1=1 → (∀ a b, 0 < a → 0 < b → F (a*b)=F a*F b) → OneBounded F →
      ∀ M : ℝ, 0 ≤ M → MRTDistanceLowerBound F X H₀ M → ∀ r : ℤ,
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) V H ((r:ℝ)/q) ≤
      Real.sqrt (q:ℝ)*((1+Real.log q)*
        (4*C*V*H*(Real.exp (-2*M/5)+
          Real.sqrt (Real.log (Real.log X)/(Real.log X)^(1/80:ℝ))+W⁻¹)+
          2*(q:ℝ)*(2*(K:ℝ)+1)*H)+(q:ℝ)*V) := by
  sorry

end OAI.TwoPointCorrelations
