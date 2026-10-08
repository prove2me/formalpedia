-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_canonical_shifted_source_deletion_uniform
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:51.618993+00:00
-- url     : https://prove2.me/theorems/8d5f105e-7839-4cd7-a46b-4f6bf4202242
-- title:
--   Under Braverman's theorem and the mod-5 prime number theorem, the canonical shifted source-deletion cost is small
-- statement:
--   Assume `BravermanDepth22Input` (Braverman's theorem for depth-22 AC⁰ circuits) and `ModFiveThetaInput` (there are $c>0$, $C\ge0$ with $|\theta_{\pm}(x)-\delta_\pm x|\le Cx\,e^{-c\sqrt{\log x}}$ for $x\ge2$, where $\theta_+(x)=\sum_{p\le x,\ p\equiv1\ (5)}\log p$ and $\theta_-(x)=\sum_{p\le x,\ p\not\equiv1\ (5)}\log p$ (`modFiveTheta`), $\delta_+=1/4$, $\delta_-=3/4$). Then there is a natural $A\ge1000$ with the following property. For every natural $h$, every finite set $E$ of naturals containing all prime divisors of $h$, and all reals $W\ge10$ and $C_{\mathrm{bins}}\ge0$, there is $C>0$ such that for all sufficiently large $L$ (with $L\ge1$), all $\eta\in(0,1]$ and $K>0$, every finite set of bins $\subseteq\mathbb Z$ with at most $\exp(C_{\mathrm{bins}}\log L)$ elements, every $c:\mathbb N\to\mathbb R$, every predicate `eligible` such that eligible pairs satisfy `PaddingPairEligible L η` and lie in the bin `actualPaddingBin η (c d) j q`, every site function and all $a,N$ with $N_j\ge\exp(L^A/2)$ on the bins: writing $J$ = `primeSupplyCount W L` and $P$ = `centeredPrimeBands E (L^{199/200}) W J`,
--
--   $$\frac{\texttt{canonicalShiftedSourceDeletion}(h,E,W,L,\eta,K,\dots)}{\texttt{paddingTiltNormalizer}(\texttt{paddingPrimeSupply }E\,L)\cdot\prod_{j}\texttt{primeHarmonicMass}(P_j)}\le 2^J\Big(\frac CK+L^{-100}+e^{-2WJ}\Big)+2e^{-L^{9/10}}.$$
--
--   All named quantities are definitions of the bundle.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_canonical_shifted_source_deletion_uniform
    (hBr : BravermanDepth22Input) (hP : ModFiveThetaInput) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ (h : ℕ) (E : Finset ℕ)
      (hE : ∀ p, p.Prime → p ∣ h → p ∈ E),
      ∀ (W Cbins : ℝ) (hW : 10 ≤ W) (_hC : 0 ≤ Cbins),
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (hL : 1 ≤ L) (η K : ℝ), 0 < η → η ≤ 1 → 0 < K →
      ∀ (bins : Finset ℤ) (c : ℕ → ℝ) (eligible : ℤ → ℕ → ℕ → Prop),
      (bins.card : ℝ) ≤ Real.exp (Cbins * Real.log L) →
      (∀ j ∈ bins, ∀ d q, eligible j d q → PaddingPairEligible L η d q) →
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (c d) j q) →
      ∀ (site : ℤ → ℕ → ℕ → ℤ) (a N : ℤ → ℕ),
      (∀ j ∈ bins, Real.exp (L ^ A / 2) ≤ (N j : ℝ)) →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      canonicalShiftedSourceDeletion h E W L η K hL (by linarith) hE bins c eligible site a N /
        (paddingTiltNormalizer (paddingPrimeSupply E L) * ∏ j, primeHarmonicMass (P j)) ≤
        (2 : ℝ) ^ J * (C / K + L ^ (-100 : ℝ) + Real.exp (-2 * W * J)) +
          2 * Real.exp (-L ^ (9 / 10 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
