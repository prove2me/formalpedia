-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_affine_bilinear_testing
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_bilinear_testing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:13.625036+00:00
-- url     : https://prove2.me/theorems/38df57a7-9b54-4aa5-89c2-b49a17a69a65
-- title:
--   Under the mod-5 prime number theorem and Braverman's theorem, bilinear testing of the prime block compression along a progression
-- statement:
--   Assume `ModFiveThetaInput` and `BravermanDepth22Input`. Then there is a natural $A\ge1000$ such that for all naturals $h,l>0$, every finite set $E$ containing the prime divisors of $h$ and of $l$, and every $W\ge1$, for all sufficiently large $L\ge1$: for every $\eta\in(0,1]$ and every eligibility relation contained in `PaddingPairEligible L η`, put $J$ = `primeSupplyCount W L`, $P$ = `centeredPrimeBands E (L^{199/200}) W J`, $Q_p$ = `paddingPrimeSupply E L`, $Q$ = `boundedPaddingDivisors Q_p ⌊100 log L⌋`, data = `canonicalTraceFamily h E W L eligible …`, keep = the non-prohibited sites (`¬ProhibitedSite h ⌊L^{1/10}⌋ (pairs of data)`), $M=\lceil e^{103L}\rceil$, $K=e^{4J}$ and $R=e\cdot2K(2e^{150}\sqrt W)^J$. Then for every symmetric gate relation, all $f,g:\mathbb Z\to\mathbb C$ bounded by $1$ and all naturals $a,N$ with $N\ge\exp(L^A/2)$,
--
--   $$\frac1N\sum_{x<N}\Big|\big\langle u_x,\ \mathcal C_{a+lx}\,v_x\big\rangle\Big|\le4\Big(3R\,l\,2M\,\texttt{paddingTiltNormalizer}(Q_p)+M\cdot2K(8W)^J\cdot5^{400\log L}\,e^{-2\lfloor L\rfloor}\Big),$$
--
--   where $u_x,v_x$ are the padding test vectors `paddingTestVector Q_p L (i ↦ i + a + lx) f` and `… g` indexed by $i<M$, and $\mathcal C_n$ = `primeBlockCompression P M Q actualPaddingCoefficient (pairs) (actualPaddingVertex Q_p) L K W (actualPaddingDegreeCut Q_p L) h gate keep n` is the bundle's compressed prime block operator.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_affine_bilinear_testing`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_affine_bilinear_testing
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
      ∀ gate : ℕ → ℤ → ℤ → Prop, (∀ d n m, gate d n m ↔ gate d m n) →
      ∀ f g : ℤ → ℂ, (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let M := ⌈Real.exp (103 * L)⌉₊
      let K := Real.exp (4 * J)
      let R := Real.exp 1 * (2 * (K * (2 * Real.exp 150 * Real.sqrt W) ^ J))
      uniformAverage (fun x : Fin N =>
        let u := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) f
        let v := paddingTestVector Qp L (fun i : Fin M => (i.val : ℤ) + (a + l * x.val : ℕ)) g
        ‖inner ℂ u (primeBlockCompression P M Q actualPaddingCoefficient
          (fun d q => (d, q) ∈ data.pairs) (actualPaddingVertex Qp)
          L K W (fun _ => actualPaddingDegreeCut Qp L) h gate keep
          (a + l * x.val : ℕ) v)‖) ≤
        4 * ((3 * R) * ((l : ℝ) * (2 * M * paddingTiltNormalizer Qp)) +
          ((M : ℝ) * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L)) *
            Real.exp (-(2 * ⌊L⌋₊ : ℕ))) := by
  sorry

end OAI.TwoPointCorrelations
