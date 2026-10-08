-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_affine_spectral_tail_uniform
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:05.351117+00:00
-- url     : https://prove2.me/theorems/f9f43c60-49cd-4ef4-af73-5640905fe83d
-- title:
--   Under the mod-5 prime number theorem and Braverman's theorem, the shifted walk matrices along a progression rarely have large spectral radius
-- statement:
--   Assume `ModFiveThetaInput` and `BravermanDepth22Input`. Then there is a natural $A\ge1000$ such that for all naturals $h>0$, $l$, every finite $E$ containing the prime divisors of $h$ and $l$, and $W\ge1$, for all sufficiently large $L\ge1$, every $\eta\in(0,1]$ and every eligibility relation contained in `PaddingPairEligible L η`: with $J,P,Q_p,Q$, data = `canonicalTraceFamily …` as in the companion statements, the weight `maskedSignedIntegerWeight Q actualPaddingCoefficient (pairs) (actualPaddingVertex Q_p) (centeredTuple ∘ primeFactors) L e^{4J} (actualPaddingDegreeCut Q_p L) h (non-prohibited sites)`, and, for each gate relation and $c\in\mathbb Z$, the matrix $\mathcal M_c$ = `shiftMatrix (primeBlockEmbedding ⌈e^{103L}⌉) (integerShiftNext Q ∏ h) (physicalShiftWeight Q ∏ h gate (weight shifted by c))`: for all naturals $a,N$ with $N\ge\exp(L^A/2)$,
--
--   $$\frac1N\#\Big\{x<N:\ \rho\big(\mathcal M_{a+lx}\big)>e\cdot2e^{4J}(2e^{150}\sqrt W)^J\Big\}\le e^{-2\lfloor L\rfloor},$$
--
--   where $\rho$ is the spectral radius of a real matrix (`realMatrixSpectralRadius`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_affine_spectral_tail_uniform
    (hprime : ModFiveThetaInput) (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧
      ∀ (h l : ℕ) (_hh : 0 < h) (E : Finset ℕ)
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
      let weight := maskedSignedIntegerWeight Q actualPaddingCoefficient
        (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
        (fun d => centeredTuple d.primeFactors) L (Real.exp (4 * J))
        (fun _ => actualPaddingDegreeCut Qp L) h
        (fun z => ¬ProhibitedSite h ⌊L ^ (1 / 10 : ℝ)⌋₊ (fun d q => (d, q) ∈ data.pairs) z)
      ∀ gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop,
      let matrix := fun c : ℤ => shiftMatrix
        (primeBlockEmbedding (P := P) ⌈Real.exp (103 * L)⌉₊)
        (integerShiftNext Q (fun d => ∏ j, (d j).val) h)
        (physicalShiftWeight Q (fun d => ∏ j, (d j).val) h gate
          (fun t n => weight t (n + c)))
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      uniformAverage (fun x : Fin N => if
        Real.exp 1 * (2 * (Real.exp (4 * J) * (2 * Real.exp 150 * Real.sqrt W) ^ J)) <
          realMatrixSpectralRadius (matrix (a + l * x.val : ℕ)) then (1 : ℝ) else 0) ≤
        Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  sorry

end OAI.TwoPointCorrelations
