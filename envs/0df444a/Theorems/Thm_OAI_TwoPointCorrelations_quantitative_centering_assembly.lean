-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_quantitative_centering_assembly
-- name    : OAI.TwoPointCorrelations.quantitative_centering_assembly
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:39.136153+00:00
-- url     : https://prove2.me/theorems/3f928465-a954-494e-a631-b700224b6df2
-- title:
--   Under three analytic inputs, the canonical raw bins reproduce the Liouville progression mean up to a power-of-L error
-- statement:
--   Assume `ModFiveThetaInput`, `PrimeReciprocalInput` and `MRTLiouvilleShortInput`. Let $h>0$, $l\ne0$, $E$ a finite set containing the prime divisors of $l$, and $W\ge1$. Then there is $C>0$ such that for all sufficiently large $L\ge1$, every $X\ge\exp(L^{1000})$, every $\eta\in(0,\log2)$ and every natural $b$, with $J$, $P$, $Q$ as usual and $S_0$ = `totalPaddingBinMass (primeTupleDivisors P) Q L η`,
--
--   $$\Big|\sum_{j\in\mathrm{bins}}\texttt{canonicalRawBin}(h,l,b,E,W,L,\eta,X,j)-S_0\,\mu_{h,l,b}(X)\Big|\le C\eta^{-1}2^JL^{-1/20}\,\texttt{paddingTiltNormalizer}(Q)\prod_i\sum_{p\in P_i}\frac1p+S_0\Big(2\eta+\frac1X\Big),$$
--
--   where bins = `paddingBinIndices L η` and $\mu_{h,l,b}(X)=\frac1X\sum_{1\le n\le\lfloor X\rfloor,\ n\equiv b\ (l)}\lambda(n)\lambda(n+h)$ (`progressionLiouvilleMean`).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.quantitative_centering_assembly`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem quantitative_centering_assembly (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTLiouvilleShortInput)
    (h : ℕ) (hh : 0 < h) (l : ℕ) [NeZero l] (E : Finset ℕ)
    (hEl : ∀ p, p.Prime → p ∣ l → p ∈ E) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop, ∀ _hL : 1 ≤ L,
      ∀ X : ℝ, Real.exp (L ^ (1000 : ℝ)) ≤ X →
      ∀ η : ℝ, 0 < η → η < Real.log 2 → ∀ b : ℕ,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      let S₀ := totalPaddingBinMass (primeTupleDivisors P) Q L η
      ‖(∑ j ∈ paddingBinIndices L η, canonicalRawBin h l b E W L η X j) -
          (S₀ : ℂ) * progressionLiouvilleMean h l b X‖ ≤
        C * η⁻¹ * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) * paddingTiltNormalizer Q *
          (∏ i, primeHarmonicMass (P i)) + S₀ * (2 * η + 1 / X) := by
  sorry

end OAI.TwoPointCorrelations
