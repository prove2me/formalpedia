-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prime_prefix_split
-- name    : OAI.ShortEgyptian.prime_prefix_split
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:46:58.33762+00:00
-- url     : https://prove2.me/theorems/bf606867-b55f-4ba0-99af-cd3367c92773
-- title:
--   Splitting an integer at a threshold along its increasing prime factorization
-- statement:
--   Let $n\ge 1$ be a natural number and let $R$ be a real number with $1\le R<n$. Then there exist natural numbers $d\ge 1$, $e\ge 1$ and a prime $p$ such that
--
--   $$
--   n=de,\qquad p\mid e,\qquad d\le R<dp,
--   $$
--
--   and moreover every prime factor of $d$ is at most $p$, while every prime factor of $e$ is at least $p$.
--
--   In words, $n$ is cut into a "prefix" $d$ built from its smallest primes and a "suffix" $e$ built from its largest primes; the prefix stays below the threshold $R$, but multiplying it by the first prime $p$ of the suffix overshoots $R$.
--
--   This decomposition is used when averaging divisor-type functions over a short interval: an integer $n>R$ is attributed to its divisor $d\le R$, while the cofactor $e$ has no prime factor below $p$, so its number of small divisors can be bounded in terms of $\log p$.
--
--   **Formalization Note** Prime factors are read from `Nat.primeFactorsList` (the prime factors listed with multiplicity), and the conditions only concern membership in that list; in particular $d=1$ is allowed, and $p$ may divide both $d$ and $e$. The inequalities $d\le R<dp$ are stated in $\mathbb{R}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/PrimeSplitting.lean#L96-L143

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

theorem OAI.ShortEgyptian.prime_prefix_split {n : ℕ} (hn : n ≠ 0) (R : ℝ) (hR : 1 ≤ R) (hnR : R < n) :
    ∃ d e p : ℕ, n = d*e ∧ d ≠ 0 ∧ e ≠ 0 ∧ p.Prime ∧ p ∣ e ∧
      (d:ℝ) ≤ R ∧ R < (d:ℝ)*p ∧
      (∀ q ∈ d.primeFactorsList, q ≤ p) ∧ (∀ q ∈ e.primeFactorsList, p ≤ q) := by sorry
