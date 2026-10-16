-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_smooth_divisor_weight
-- name    : OAI.ShortEgyptian.smooth_divisor_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:41:25.955966+00:00
-- url     : https://prove2.me/theorems/892c26f0-8f94-46b2-80e8-50e6d3fb911e
-- title:
--   Euler-product bound for $\sum\tau(d)^r d^{-\sigma}$ over integers with prime factors in $P$
-- statement:
--   For a positive integer $d$ let $\tau(d)$ be the number of its positive divisors. For an integer $r\ge0$ let $C_r=\sum_{j\ge0}(j+2)^r(3/4)^j$. Let $P$ be a finite set of natural numbers, and let $s$ be a finite set of positive integers each of whose prime factors belongs to $P$. Then for every real $\sigma\ge\frac12$,
--
--   $$
--   \sum_{d\in s}\frac{\tau(d)^r}{d^{\sigma}}\;\le\;\exp\Bigl(C_r\sum_{\substack{p\in P\\ p\ \text{prime}}}p^{-\sigma}\Bigr).
--   $$
--
--   The bound does not depend on $s$; since the terms are nonnegative, it is equivalent to the same bound for the full sum over all positive integers whose prime factors lie in $P$ (which therefore converges). It controls weighted moments of the divisor function over smooth numbers, the prime sum on the right being estimated separately.
--
--   **Formalization Note** The weight is `divisorWeight r σ d = (d.divisors.card : ℝ) ^ r * (d : ℝ) ^ (-σ)`, and $C_r$ is `momentSeriesConst r`. The hypothesis is `d ∈ Nat.factoredNumbers P`, i.e. $d\neq0$ and every prime factor of $d$ lies in $P$; elements of $P$ that are not prime are ignored on the right-hand side.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean#L96-L121

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.smooth_divisor_weight (r : ℕ) {σ : ℝ} (hσ : 1/2 ≤ σ)
    (s P : Finset ℕ) (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P) :
    ∑ d ∈ s, divisorWeight r σ d ≤
      Real.exp (momentSeriesConst r * ∑ p ∈ P with p.Prime, (p:ℝ)^(-σ)) := by sorry
