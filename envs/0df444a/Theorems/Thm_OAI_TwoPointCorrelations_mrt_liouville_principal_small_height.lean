-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_mrt_liouville_principal_small_height
-- name    : OAI.TwoPointCorrelations.mrt_liouville_principal_small_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:11.503515+00:00
-- url     : https://prove2.me/theorems/887fc35b-38c3-4868-84bb-3d289a033b89
-- title:
--   The prime tail sum of p^{it}/p twisted by a principal character is bounded below
-- statement:
--   There is $C\ge0$ such that for all sufficiently large $X$, every $q$ with $1\le q\le(\log X)^{1/125}$ and every real $t$ with $|t|\le\exp((\log X)^{1/3})$,
--
--   $$\operatorname{Re}\sum_{p\in\mathcal T(X)}\frac{\chi_0(p)\,p^{it}}{p}\ge-C,$$
--
--   where $\chi_0$ is the principal character modulo $q$, the term is `characterTwist χ₀ t p / p` $=\chi_0(p)e^{it\log p}/p$, and $\mathcal T(X)$ = `mrtLiouvillePrimeTail X` = `mrtPrimePowerTail (3/4) X` is the bundle's set of tail primes.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.mrt_liouville_principal_small_height`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset
open scoped Classical
open scoped Topology

theorem mrt_liouville_principal_small_height : ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ X : ℕ in atTop, ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 125 : ℝ) →
      ∀ t : ℝ, |t| ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 / 3 : ℝ)) →
        -C ≤ (∑ p ∈ mrtLiouvillePrimeTail X,
          characterTwist (1 : DirichletCharacter ℂ q) t p / (p : ℂ)).re := by
  sorry

end OAI.TwoPointCorrelations
