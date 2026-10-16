-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prime_reciprocals_dyadic
-- name    : OAI.ShortEgyptian.prime_reciprocals_dyadic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:38:48.593383+00:00
-- url     : https://prove2.me/theorems/26823cfd-44b4-471d-bfbb-50f75e3164f7
-- title:
--   Dyadic bound $\sum_{p\le 2^{K+1}}1/p\le 4(1+H_K)$ for prime reciprocals
-- statement:
--   For an integer $K\ge0$ let $H_K=\sum_{j=1}^{K}\frac1j$ be the $K$-th harmonic number (so $H_0=0$). Then the sum of the reciprocals of the primes up to $2^{K+1}$ satisfies
--
--   $$
--   \sum_{\substack{p\le 2^{K+1}\\ p\ \text{prime}}}\frac1p\;\le\;4\,(1+H_K).
--   $$
--
--   Since $H_K\le1+\log K$, this is an explicit upper bound of the form $\sum_{p\le x}1/p\le4\log\log x+O(1)$, with all constants explicit. It is the dyadic form from which a bound for $\sum_{p\le T}1/p$ at arbitrary $T$ is derived.
--
--   **Formalization Note** The primes up to $n$ form `Nat.primesLE n`; $H_K$ is Mathlib's `harmonic K` (a rational number, cast to the reals).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeReciprocals.lean#L37-L82

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

theorem OAI.ShortEgyptian.prime_reciprocals_dyadic (K : ℕ) :
    ∑ p ∈ Nat.primesLE (2 ^ (K + 1)), (1 : ℝ) / p ≤ 4 * (1 + (harmonic K : ℝ)) := by sorry
