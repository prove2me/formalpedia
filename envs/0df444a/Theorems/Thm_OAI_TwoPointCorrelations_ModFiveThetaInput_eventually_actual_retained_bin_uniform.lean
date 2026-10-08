-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_retained_bin_uniform
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_retained_bin_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:15:27.18036+00:00
-- url     : https://prove2.me/theorems/0912be34-37f1-4f33-b32d-46755ed8bf2f
-- title:
--   Under the mod-5 prime number theorem and Braverman's theorem, the retained prime prefix along a progression gate is O(l²/L)
-- statement:
--   Assume `ModFiveThetaInput` and `BravermanDepth22Input`. Then there is a natural $A\ge1000$ such that for all naturals $h,l>0$, every finite $E$ containing the prime divisors of $h$ and $l$, and $W\ge1$, for all sufficiently large $L\ge1$, every $\eta\in(0,1]$ and every eligibility relation contained in `PaddingPairEligible L η`: with $J,P,Q_p,Q$, data = `canonicalTraceFamily h E W L eligible …`, keep = non-prohibited sites, $K=e^{4J}$ and $R=e\cdot2K(2e^{150}\sqrt W)^J$, for all naturals $b,N$ with $N\ge\exp(L^A/2)$,
--
--   $$\Big|\texttt{retainedPrimePrefix}\ P\ Q\ Q_p\ (\dots)\ L\ K\ W\ (\dots)\ h\ (\texttt{progressionEdgeGate}\ h\ l\ b)\ \mathrm{keep}\ N\Big|\le\frac{3l^2\,\texttt{paddingTiltNormalizer}(Q_p)\,R}{L}+3e^{-L}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_retained_bin_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_retained_bin_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (_hl : 0 < l) (E : Finset ℕ)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E)
    (_hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W),
      ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η : ℝ), 0 < η → η ≤ 1 →
      ∀ eligible : ℕ → ℕ → Prop,
      (∀ d q, eligible d q → PaddingPairEligible L η d q) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Qp := paddingPrimeSupply E L
      let Q := boundedPaddingDivisors Qp ⌊100 * Real.log L⌋₊
      let data := canonicalTraceFamily h E W L eligible hL hW hE
      let keep := fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊
        (fun d q => (d, q) ∈ data.pairs) z
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      ‖retainedPrimePrefix P Q Qp actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
        h (progressionEdgeGate h l b) keep N‖ ≤
      3 * (l : ℝ) ^ 2 * paddingTiltNormalizer Qp * R / L + 3 * Real.exp (-L) := by
  sorry

end OAI.TwoPointCorrelations
