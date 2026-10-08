-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_progression_block_testing_uniform
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_progression_block_testing_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:53.655837+00:00
-- url     : https://prove2.me/theorems/469d9750-3705-43e1-bbc8-38e2cbfbc316
-- title:
--   Under the mod-5 prime number theorem and Braverman's theorem, the Liouville block form tested along a progression gate
-- statement:
--   Assume `ModFiveThetaInput` and `BravermanDepth22Input`. Then there is a natural $A\ge1000$ such that for all naturals $h,l>0$, every finite $E$ containing the prime divisors of $h$ and $l$, and $W\ge1$, for all sufficiently large $L\ge1$, every $\eta\in(0,1]$ and every eligibility relation contained in `PaddingPairEligible L η`: with $J,P,Q_p,Q$, data = `canonicalTraceFamily …`, keep = non-prohibited sites, for all naturals $b,N$ with $N\ge\exp(L^A/2)$, $M=\lceil e^{103L}\rceil$, $K=e^{4J}$, $R=e\cdot2K(2e^{150}\sqrt W)^J$:
--
--   $$\frac1{lN}\sum_{t<lN}\Big|\texttt{ambientLiouvilleBlockForm}\ P\ M\ Q\ Q_p\ (\dots)\ L\ K\ W\ (\dots)\ h\ (\texttt{progressionEdgeGate}\ h\ l\ b)\ \mathrm{keep}\ t\Big|\le3R\,l\,2M\,\texttt{paddingTiltNormalizer}(Q_p)+M\cdot2K(8W)^J\cdot5^{400\log L}\,e^{-2\lfloor L\rfloor}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_progression_block_testing_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_progression_block_testing_uniform
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
      ∀ b N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun t : Fin (l * N) =>
        ‖ambientLiouvilleBlockForm P M Q Qp actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) L K W (fun _ => actualPaddingDegreeCut Qp L)
          h (progressionEdgeGate h l b) keep t.val‖) ≤
        (3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ)) := by
  sorry

end OAI.TwoPointCorrelations
