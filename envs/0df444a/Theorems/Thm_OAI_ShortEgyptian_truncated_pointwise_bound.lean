-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_truncated_pointwise_bound
-- name    : OAI.ShortEgyptian.truncated_pointwise_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:45:40.954459+00:00
-- url     : https://prove2.me/theorems/7dff0da4-a135-4dd9-8a12-d7ce31eca661
-- title:
--   Pointwise bound for the truncated divisor count via a smooth–rough factorization
-- statement:
--   For a positive integer $n$ and a real number $X$ let $\tau_X(n)=\#\{a\in\mathbb{N}:\ a\mid n,\ a\le X\}$ be the number of divisors of $n$ that are at most $X$. Let $n\ge1$, and let $X$, $W$, $z$ and $q$ be real numbers with
--   $$z>1,\qquad 0<q<1,\qquad \log n\le W .$$
--   Then
--
--   $$
--   \tau_X(n)\;\le\;\exp\!\left(z\,\log\Bigl(1+\frac{W}{\log2}\Bigr)+\frac{qW-\log X\cdot\log q}{\log z}\right).
--   $$
--
--   No condition on the prime factors of $n$ is imposed: the first term in the exponent accounts for the prime factors below $z$, the second for those at least $z$. With $W$ an upper bound for $\log n$ and suitable choices of the parameters $z$ and $q$, this gives a pointwise bound on $\tau_X(n)$ that is uniform over all $n$ with $\log n\le W$, as needed for moment estimates of truncated divisor counts over intervals.
--
--   **Formalization Note** $\tau_X(n)$ is `truncatedDivisorCount X n`; $\log$ is `Real.log` (here $W\ge\log n\ge0$, so the argument $1+W/\log2$ is at least $1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeSplitting.lean#L77-L94

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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.truncated_pointwise_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1) (hW : Real.log n ≤ W) :
    (truncatedDivisorCount X n:ℝ) ≤ Real.exp
      (z * Real.log (1+W/Real.log 2) + (q*W-Real.log X*Real.log q)/Real.log z) := by sorry
