-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_actual_pool_masses
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_pool_masses
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:41.112595+00:00
-- url     : https://prove2.me/theorems/73baba18-df6b-46cd-8998-4ce25c1f3484
-- title:
--   Under the mod-5 prime number theorem, the harmonic masses of the centered prime bands and pools
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals and $W\ge1$. Then for all sufficiently large $L$, with $J$ = `primeSupplyCount W L` $=\lfloor\frac{\log L}{1200W}\rfloor$ and $A=L^{199/200}$:
--
--   - $J\ge1$;
--   - for each band $P_j$ = `centeredPrimeBands E A W J j`, $1\le\sum_{p\in P_j}1/p\le2W$ and $\sum_{p\in P_j}1/p\le L^2$;
--   - for the pool $P$ = `centeredPrimePool E A W J`, $1\le\sum_{p\in P}1/p\le\frac{\log L}{600}$ and $\sum_{p\in P}1/p\le L^2$;
--   - $\sum_{p\in\texttt{paddingPrimeSupply }E\,L}1/p\le L^2$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_actual_pool_masses`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_actual_pool_masses (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let A := L ^ (199 / 200 : ℝ)
      1 ≤ J ∧
      (∀ j : Fin J, 1 ≤ primeHarmonicMass (centeredPrimeBands E A W J j) ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ 2 * W ∧
        primeHarmonicMass (centeredPrimeBands E A W J j) ≤ L ^ (2 : ℕ)) ∧
      1 ≤ primeHarmonicMass (centeredPrimePool E A W J) ∧
      primeHarmonicMass (centeredPrimePool E A W J) ≤ Real.log L / 600 ∧
      primeHarmonicMass (centeredPrimePool E A W J) ≤ L ^ (2 : ℕ) ∧
      primeHarmonicMass (paddingPrimeSupply E L) ≤ L ^ (2 : ℕ) := by
  sorry

end OAI.TwoPointCorrelations
