-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_actual_band_interval_density
-- name    : OAI.TwoPointCorrelations.mrt_actual_band_interval_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:14:17.895751+00:00
-- url     : https://prove2.me/theorems/e029e43c-87a8-4e8e-b8a9-5151146564b8
-- title:
--   Most integers in a long interval have a prime factor in each Matomäki–Radziwiłł band
-- statement:
--   There is $C>0$ such that for all sufficiently large natural $X$: for reals $2\le P\le Q$ with $\log Q\ge1$ and every $J$ with $\exp(j^{4j+2}(\log Q)^j)\le\exp(\frac12\sqrt{\log X})$ for $j=1..J$, and all naturals $A$ and $N\ge X$ (with $N\ne0$),
--
--   $$\frac1N\#\Big\{0\le n<N:\ A+n\text{ is not typical}\Big\}\le C\,\frac{\log P}{\log Q},$$
--
--   where $m$ is typical (`mrtTypical`) if for every $j\in\{1..J\}$ some prime in the band $(\mathrm{lo}_j,\mathrm{up}_j]$, $\mathrm{lo}_j=\exp(j^{4j}(\log Q)^{j-1}\log P)$, $\mathrm{up}_j=\exp(j^{4j+2}(\log Q)^j)$, divides $m$ (the bands are `mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)`, the primes $p$ with $\mathrm{lo}_j<p\le\mathrm{up}_j$ of the bundle's sieve prime sets).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_actual_band_interval_density`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset
open scoped Classical

theorem mrt_actual_band_interval_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P Q : ℝ) (J : ℕ), 2 ≤ P → P ≤ Q → 1 ≤ Real.log Q →
      (∀ j ∈ Icc 1 J, mrtBandUpper Q j ≤
        Real.exp (Real.sqrt (Real.log (X:ℝ))/2)) →
      ∀ (A N : ℕ) [NeZero N], X ≤ N →
      (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical (Icc 1 J)
          (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j))
          (A+n.val)) ≤ C*Real.log P/Real.log Q := by
  sorry

end OAI.TwoPointCorrelations
