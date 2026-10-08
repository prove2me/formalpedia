-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_complex_bin
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_complex_bin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:50.802803+00:00
-- url     : https://prove2.me/theorems/eb0d1b2e-ac4a-471c-bbda-cbe075b97513
-- title:
--   Under the mod-5 prime number theorem and Braverman's theorem, the retained complex prefix of one dyadic bin is O(1/L)
-- statement:
--   Assume `ModFiveThetaInput` and `BravermanDepth22Input`. Then there is a natural $A\ge1000$ such that for every natural $h>0$, every finite $E$ containing the prime divisors of $h$, and $W\ge1$, for all sufficiently large $L\ge1$: for every $\eta\in(0,1]$, every eligibility relation contained in `PaddingPairEligible L η`, and every integer $D>0$ with $D\le hqd<2D$ for every eligible pair $(d,q)$; with $J,P,Q_p,Q$, data = `canonicalTraceFamily …`, active = the pairs of data, keep = non-prohibited sites, $K=e^{4J}$ and $R=e\cdot2K(2e^{150}\sqrt W)^J$; for all $F,G:\mathbb Z\to\mathbb C$ bounded by $1$ and every $N\ge\exp(L^A/2)$,
--
--   $$\Big|\texttt{retainedComplexPrefix}\ P\ Q\ Q_p\ (\dots)\ \mathrm{active}\ L\ K\ W\ (\dots)\ h\ (\text{always true})\ \mathrm{keep}\ F\ G\ N\Big|\le\frac{240\,\texttt{paddingTiltNormalizer}(Q_p)\,R}{L}+240e^{-L}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_complex_bin`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_complex_bin
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h : ℕ) (_hh : 0 < h) (E : Finset ℕ)
        (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      ∀ (D : ℤ), 0 < D →
      (∀ d q, eligible d q → D ≤ (h * q * d : ℕ) ∧ (h * q * d : ℕ) < 2 * D) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let active := fun d q => (d, q) ∈ data.pairs
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ active z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ (F G : ℤ → ℂ), (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) →
      ∀ N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedComplexPrefix P Q Qp actualPaddingCoefficient active L K W
        (fun _ => actualPaddingDegreeCut Qp L) h (fun _ _ _ => True) keep F G N‖ ≤
        240 * paddingTiltNormalizer Qp * R / L + 240 * Real.exp (-L) := by
  sorry

end OAI.TwoPointCorrelations
