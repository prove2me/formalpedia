-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_canonical_raw_pair_selection
-- name    : OAI.TwoPointCorrelations.canonical_raw_pair_selection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:30.279425+00:00
-- url     : https://prove2.me/theorems/53742091-0ab4-49d5-a6f1-d284fa7c2af4
-- title:
--   Under the mod-5 prime number theorem, a selection of raw complex pairs with large coefficient and small prime cost
-- statement:
--   Assume `ModFiveThetaInput` (the prime number theorem with error $Cx\,e^{-c\sqrt{\log x}}$ for the two weighted classes of primes modulo 5, as defined in the bundle). Let $f,g:\mathbb N\to\mathbb C$ be multiplicative (on coprime positive arguments) with $f(1)=g(1)=1$ and $|f(n)|,|g(n)|\le1$ for $n\ge1$, and suppose $\sum_p(1-|f(p)|)/p$ and $\sum_p(1-|g(p)|)/p$ converge (sums over primes). Let $h\ge1$, $W\ge1$ and $\gamma>0$. Then there is a finite set $E$ of naturals containing every prime divisor of $h$ such that for all sufficiently large $L\ge1$ and every $\eta>0$, writing $J$ = `primeSupplyCount W L` $=\lfloor(\tfrac1{200}\log L)/(6W)\rfloor$, $P$ = `centeredPrimeBands E (L^{199/200}) W J`, $Q$ = `paddingPrimeSupply E L` and $S_0$ = `totalPaddingBinMass (primeTupleDivisors P) Q L η`:
--
--   $S_0>0$, and there is a subset $A$ of the eligible complex pairs `eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η)` with
--
--   $$\frac{S_0}{8}\le\big\|\texttt{selectedRawCoefficient}\ A\ f\ g\big\|,\qquad\sum_{(d,q)\in A}w(d,q)\le S_0,\qquad\sum_{(d,q)\in A}w(d,q)\sum_{p\mid dq}\frac1p\le\frac{\gamma S_0}{128},$$
--
--   where $w$ = `complexPairWeight` and the inner sum is over the distinct prime factors of $dq$. All named objects are definitions of the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.canonical_raw_pair_selection`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem canonical_raw_pair_selection (hP : ModFiveThetaInput) {f g : ℕ → ℂ}
    (hfm : Multiplicative f) (hgm : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hf : OneBounded f) (hg : OneBounded g)
    (hsf : Summable (fun p : ℕ => if p.Prime then (1 - ‖f p‖) / (p : ℝ) else 0))
    (hsg : Summable (fun p : ℕ => if p.Prime then (1 - ‖g p‖) / (p : ℝ) else 0))
    (h : ℕ) (hh : 0 < h) (W γ : ℝ) (hW : 1 ≤ W) (hγ : 0 < γ) :
    ∃ E : Finset ℕ, (∀ p, p.Prime → p ∣ h → p ∈ E) ∧
      ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L, ∀ η : ℝ, 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      0 < S₀ ∧ ∃ A ⊆ eligibleComplexPairs (primeTupleDivisors P) Q (PaddingPairEligible L η),
        S₀ / 8 ≤ ‖selectedRawCoefficient A f g‖ ∧
        (∑ dq ∈ A, complexPairWeight dq) ≤ S₀ ∧
        (∑ dq ∈ A, complexPairWeight dq *
          ∑ p ∈ (dq.1 * dq.2).primeFactors, 1 / (p : ℝ)) ≤ γ * S₀ / 128 := by
  sorry

end OAI.TwoPointCorrelations
