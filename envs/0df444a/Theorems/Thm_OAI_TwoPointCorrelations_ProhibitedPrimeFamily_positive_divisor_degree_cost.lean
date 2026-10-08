-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_ProhibitedPrimeFamily_positive_divisor_degree_cost
-- name    : OAI.TwoPointCorrelations.ProhibitedPrimeFamily.positive_divisor_degree_cost
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:11:55.741989+00:00
-- url     : https://prove2.me/theorems/5db53a61-f5c0-45f5-9238-d7542513a16d
-- title:
--   The model cost of paddings whose integer has unusually many prime factors from the pool
-- statement:
--   Let `data` be a prohibited prime family (`ProhibitedPrimeFamily h J M`) whose primes are at most $B$; let $S\subseteq$ data.P, $q$ a retained divisor of data.Q (`retainedPrimeDivisors data.Q`), $W\ge10$ with $\sum_{p\in\mathrm{data}.P}1/p\le2W\,\#S$, and an integer site. Then, with $y_x$ = `data.residueOrigin x + site` and the expectation over `data.residueLaw B hB`,
--
--   $$\mathbb E_x\Big[4^{\omega(q)}\prod_{p\in S}\Big(\mathbf 1_{p\mid y_x}+\frac1p\Big)\cdot\mathbf 1\big\{q\mid y_x,\ \#\{p\in\mathrm{data}.P:p\mid y_x\}>6W\#S\big\}\Big]\le\frac{4^{\omega(q)}}q\prod_{p\in S}\frac2p\cdot e^{-2W\#S},$$
--
--   where $4^{\omega(q)}$ = `actualPaddingCoefficient q`, the product is `positivePrimeWeight S y`, $\prod_{p\in S}2/p$ is `positivePrimeNormalizer S`, and the count is `actualPaddingDegree data.P y`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.ProhibitedPrimeFamily.positive_divisor_degree_cost`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations.ProhibitedPrimeFamily

open Finset
open Filter
open scoped Classical
variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

theorem positive_divisor_degree_cost (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q)
    (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight S (data.residueOrigin x + site) *
        if (q : ℤ) ∣ data.residueOrigin x + site ∧
          6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      actualPaddingCoefficient q / q * positivePrimeNormalizer S *
        Real.exp (-2 * W * S.card) := by
  sorry

end OAI.TwoPointCorrelations.ProhibitedPrimeFamily
