-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_canonical_retained_mass
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_retained_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:30.765148+00:00
-- url     : https://prove2.me/theorems/91357c93-4b2b-4ee9-87ad-6af06cf342b1
-- title:
--   Under the mod-5 prime number theorem, the total padding bin mass is at least half of its natural size
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals and $W\ge1$. Then for all sufficiently large $L\ge1$ and every $\eta>0$, with $J$ = `primeSupplyCount W L`, $P_j$ = `centeredPrimeBands E (L^{199/200}) W J j` and $V=\prod_j\sum_{p\in P_j}1/p$:
--
--   $$W^J\le V\qquad\text{and}\qquad\frac{\texttt{paddingTiltNormalizer}(Q)\cdot V}2\le\texttt{totalPaddingBinMass}\big(\texttt{primeTupleDivisors }P,\ Q,\ L,\ \eta\big),$$
--
--   with $Q$ = `paddingPrimeSupply E L` and `paddingTiltNormalizer Q` $=\prod_{p\in Q}(1+4/p)$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_canonical_retained_mass`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_retained_mass
    (hprime : ModFiveThetaInput) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (_hL : 1 ≤ L) (η : ℝ), 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let V := ∏ j, primeHarmonicMass (P j)
      W ^ J ≤ V ∧
        paddingTiltNormalizer (paddingPrimeSupply E L) * V / 2 ≤
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η := by
  sorry

end OAI.TwoPointCorrelations
