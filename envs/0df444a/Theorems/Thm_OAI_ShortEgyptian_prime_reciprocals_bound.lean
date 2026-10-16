-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prime_reciprocals_bound
-- name    : OAI.ShortEgyptian.prime_reciprocals_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:39:29.92982+00:00
-- url     : https://prove2.me/theorems/faf34393-989e-417b-8e7e-c6817337d40d
-- title:
--   Explicit bound $\sum_{p\le T}1/p\le 8+4\log(1+\log_2 T)$
-- statement:
--   Let $T\ge2$ be an integer. Then the sum of the reciprocals of the primes up to $T$ satisfies
--
--   $$
--   \sum_{\substack{p\le T\\ p\ \text{prime}}}\frac1p\;\le\;8+4\log\Bigl(1+\frac{\log T}{\log 2}\Bigr),
--   $$
--
--   where $\log$ is the natural logarithm (so $\log T/\log2=\log_2T$).
--
--   This is an explicit, Mertens-type upper bound $\sum_{p\le T}1/p\le4\log\log T+O(1)$ valid for every $T\ge2$, with no unspecified constants. It feeds bounds on sums of divisor-function weights over integers up to $T$, where the sum of $p^{-1}$ (or of $p^{-\sigma}$) over primes enters through Euler products.
--
--   **Formalization Note** The primes up to $T$ form `Nat.primesLE T`, and the logarithm is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeReciprocals.lean#L84-L105

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.prime_reciprocals_bound (T : ℕ) (hT : 2 ≤ T) :
    ∑ p ∈ Nat.primesLE T, (1 : ℝ) / p ≤
      8 + 4 * Real.log (1 + Real.log T / Real.log 2) := by sorry
