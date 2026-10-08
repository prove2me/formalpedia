-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ModFiveThetaInput_actual_family_padding_large_bin_cut
-- name    : OAI.TwoPointCorrelations.ModFiveThetaInput.actual_family_padding_large_bin_cut
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:15:44.483836+00:00
-- url     : https://prove2.me/theorems/a1fe0d41-008a-41a0-aad8-49e2d3eabac4
-- title:
--   Under the mod-5 prime number theorem, the large-density padding bins carry tilted mass at most C/K
-- statement:
--   Assume `ModFiveThetaInput`. Let $E$ be a finite set of naturals. Then there is $C>0$ such that for all reals $L\ge1$, $\eta\in(0,1]$, $c$, $K>0$, naturals $h,J,M,B$, every prohibited prime family `data` (`ProhibitedPrimeFamily h J M`) with data.Q = `paddingPrimeSupply E L` (the primes $p\le e^L$ with $p\not\equiv1\pmod5$, minus $E$) and primes at most $B$, every integer site, finite set of bins $\subseteq\mathbb Z$, and set $D$ of retained divisors of data.Q:
--
--   $$\frac{1}{\texttt{paddingTiltNormalizer}(\mathrm{data}.Q)}\,\mathbb E_x\Big[v(y_x)^2\sum_{j\in\mathrm{bins}}\rho_j(y_x)\,\mathbf 1\{\rho_j(y_x)>K/L\}\Big]\le\frac CK,$$
--
--   where $y_x$ = `data.residueOrigin x + site`, the expectation is over `data.residueLaw B hB`, $v$ = `actualPaddingVertex data.Q`, and $\rho_j(n)$ = `paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j) v n` $=\sum_{q\in D,\ q\text{ in bin }j,\ q\mid n}u(q)/v(n)^2$ with $u$ = `actualPaddingCoefficient`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ModFiveThetaInput.actual_family_padding_large_bin_cut`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem ModFiveThetaInput.actual_family_padding_large_bin_cut (hP : ModFiveThetaInput)
    (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L η c K : ℝ) (h J M B : ℕ)
      (data : ProhibitedPrimeFamily h J M), data.Q = paddingPrimeSupply E L →
      ∀ (site : ℤ) (bins : Finset ℤ), 1 ≤ L → 0 < η → η ≤ 1 → 0 < K →
      ∀ (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
        (D : Finset ℕ), D ⊆ retainedPrimeDivisors data.Q →
      (data.residueLaw B hB).average (fun x =>
        (actualPaddingVertex data.Q (data.residueOrigin x + site)) ^ 2 *
          ∑ j ∈ bins, if K / L < paddingDensity D actualPaddingCoefficient
            (actualPaddingBin η c j) (actualPaddingVertex data.Q) (data.residueOrigin x + site)
            then paddingDensity D actualPaddingCoefficient (actualPaddingBin η c j)
              (actualPaddingVertex data.Q) (data.residueOrigin x + site) else 0) /
                paddingTiltNormalizer data.Q ≤ C / K := by
  sorry

end OAI.TwoPointCorrelations
