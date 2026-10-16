-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_truncatedDivisors_mul
-- name    : OAI.ShortEgyptian.truncatedDivisors_mul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:43:22.025837+00:00
-- url     : https://prove2.me/theorems/de23fa67-e492-410a-b451-3ff8d2593b8d
-- title:
--   Submultiplicativity of the truncated divisor count: $\tau_X(de)\le\tau(d)\,\tau_X(e)$
-- statement:
--   For a positive integer $n$ let $\tau(n)$ be the number of positive divisors of $n$, and for a real number $X$ let
--   $$\tau_X(n)=\#\{\,a\in\mathbb{N}:\ a\mid n,\ a\le X\,\}$$
--   be the number of divisors of $n$ that are at most $X$. Then for every real $X$ and all positive integers $d$ and $e$ (not necessarily coprime),
--
--   $$
--   \tau_X(de)\;\le\;\tau(d)\,\tau_X(e).
--   $$
--
--   The truncation is kept entirely on the factor $e$, while $d$ is paid for by its full divisor count. This is useful when $d$ has few divisors for structural reasons (for example, when it is composed of small primes only) and the truncation is to be exploited on the remaining factor $e$.
--
--   **Formalization Note** $\tau_X(n)$ is `truncatedDivisorCount X n`, the cardinality of `truncatedDivisors X n`, the divisors `a` of `n` with `(a : ℝ) ≤ X`; $\tau(d)$ is `d.divisors.card`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean#L16-L32

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

theorem OAI.ShortEgyptian.truncatedDivisors_mul (X : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    truncatedDivisorCount X (d*e) ≤ d.divisors.card * truncatedDivisorCount X e := by sorry
