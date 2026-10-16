-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_rough_cardFactors_log
-- name    : OAI.ShortEgyptian.rough_cardFactors_log
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:43:58.56797+00:00
-- url     : https://prove2.me/theorems/62aedee2-f6d0-4f98-97b8-ba5e09d94930
-- title:
--   Integers with all prime factors at least $z$ satisfy $\Omega(n)\log z\le\log n$
-- statement:
--   For a positive integer $n$ let $\Omega(n)$ be the number of prime factors of $n$ counted with multiplicity (so $\Omega(12)=3$). Let $n\ge1$ and let $z>0$ be a real number such that every prime factor $p$ of $n$ satisfies $p\ge z$. Then
--
--   $$
--   \Omega(n)\,\log z\;\le\;\log n .
--   $$
--
--   For $z>1$ this says that an integer whose prime factors are all at least $z$ (a $z$-rough integer) has at most $\log n/\log z$ prime factors. This is the basic input for bounding the number of divisors of rough integers, and with $z=2$ it gives $\Omega(n)\le\log n/\log2$ for every $n\ge1$.
--
--   **Formalization Note** $\Omega$ is `ArithmeticFunction.cardFactors`, the roughness hypothesis ranges over `n.primeFactorsList` (the prime factors with multiplicity), and $\log$ is `Real.log`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/TruncatedDivisors.lean#L34-L49

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

theorem OAI.ShortEgyptian.rough_cardFactors_log {n : ℕ} (hn : n ≠ 0) (z : ℝ) (hz : 0 < z)
    (hrough : ∀ p ∈ n.primeFactorsList, z ≤ p) :
    (ArithmeticFunction.cardFactors n : ℝ) * Real.log z ≤ Real.log n := by sorry
