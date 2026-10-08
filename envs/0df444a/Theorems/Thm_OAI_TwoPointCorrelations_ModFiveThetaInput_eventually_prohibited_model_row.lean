-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_eventually_prohibited_model_row
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_prohibited_model_row
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:23.819914+00:00
-- url     : https://prove2.me/theorems/66608bd9-53de-4c87-9d3e-f6d3f7a6d6c8
-- title:
--   Under the mod-5 prime number theorem, the model average of a prohibited positive row is at most exp(−L^{9/10})
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals, $W\ge10$ and $C\ge0$. Then for all sufficiently large $L$: for every prohibited prime family `data` (`ProhibitedPrimeFamily h J M` with $J$ = `primeSupplyCount W L`) with data.P = `centeredPrimePool E (L^{199/200}) W J`, data.Q = `paddingPrimeSupply E L`, primes at most $B$, and deleted event of probability at most $\exp(-\frac12L^{199/200})$ under `data.residueLaw B hB`; every $D\subseteq$ `primeTupleDivisors (centeredPrimeBands E (L^{199/200}) W J)`; every assignment of a set of retained divisors of data.Q to each $d\in D$; every $A\in[0,\exp(C\log L)]$ and every integer site:
--
--   $$A\cdot\mathbb E_x\,\texttt{prohibitedPositiveRow}(\mathrm{data},s,D,\mathrm{padding},\mathrm{data.residueOrigin}\,x+\mathrm{site})\le\exp(-L^{9/10}).$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.eventually_prohibited_model_row`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_prohibited_model_row (hP : ModFiveThetaInput)
    (E : Finset ℕ) (W C : ℝ) (hW : 10 ≤ W) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (h M B s : ℕ)
      (data : ProhibitedPrimeFamily h (primeSupplyCount W L) M),
      data.P = centeredPrimePool E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L) →
      data.Q = paddingPrimeSupply E L →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B),
      (data.residueLaw B hB).probability (data.deletedEvent s B) ≤
        Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) →
      ∀ (D : Finset ℕ), D ⊆ primeTupleDivisors
        (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)) →
      ∀ (padding : ℕ → Finset ℕ),
      (∀ d ∈ D, padding d ⊆ retainedPrimeDivisors data.Q) →
      ∀ (A : ℝ), 0 ≤ A → A ≤ Real.exp (C * Real.log L) → ∀ site : ℤ,
      A * (data.residueLaw B hB).average (fun x =>
        prohibitedPositiveRow data s D padding (data.residueOrigin x + site)) ≤
          Real.exp (-L ^ (9 / 10 : ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
