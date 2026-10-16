-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_rough_truncated_bound
-- name    : OAI.ShortEgyptian.rough_truncated_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:44:27.6015+00:00
-- url     : https://prove2.me/theorems/c5d3316d-6abd-4005-adf4-8e649f5070dd
-- title:
--   Bound for the truncated divisor count of a $z$-rough integer
-- statement:
--   For a positive integer $n$ and a real number $X$ let $\tau_X(n)=\#\{a\in\mathbb{N}:\ a\mid n,\ a\le X\}$ be the number of divisors of $n$ that are at most $X$. Let $n\ge1$, and let $X$, $W$, $z$ and $q$ be real numbers with
--   $$z>1,\qquad 0<q<1,\qquad \log n\le W,$$
--   such that every prime factor $p$ of $n$ satisfies $p\ge z$. Then
--
--   $$
--   \tau_X(n)\;\le\;\exp\!\left(\frac{qW-\log X\cdot\log q}{\log z}\right).
--   $$
--
--   Since $\log q<0$, the term $-\log X\cdot\log q=\log X\cdot\log(1/q)$ is the price of the truncation level $X$, while $qW$ reflects the total size of $n$; the free parameter $q$ balances the two. For comparison, the full divisor count satisfies $\tau(n)\le2^{\Omega(n)}\le\exp(W\log2/\log z)$, where $\Omega(n)$ is the number of prime factors of $n$ counted with multiplicity; the truncated count can be much smaller when $\log X$ is small compared with $W$, and the parameter $q$ is chosen to exploit this.
--
--   **Formalization Note** $\tau_X(n)$ is `truncatedDivisorCount X n`; roughness is stated for every element of `n.primeFactorsList`. `Real.log` is defined for all reals (with $\log0=0$ and $\log x=\log|x|$); if $X<1$ then $\tau_X(n)=0$ and the statement is trivial, so only $X\ge1$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean#L116-L172

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

theorem OAI.ShortEgyptian.rough_truncated_bound {n : ℕ} (hn : n ≠ 0) (X W z q : ℝ)
    (hz : 1 < z) (hq0 : 0 < q) (hq1 : q < 1)
    (hW : Real.log n ≤ W) (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (truncatedDivisorCount X n : ℝ) ≤
      Real.exp ((q * W - Real.log X * Real.log q) / Real.log z) := by sorry
