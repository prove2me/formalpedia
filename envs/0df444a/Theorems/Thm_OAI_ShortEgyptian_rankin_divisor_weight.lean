-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_rankin_divisor_weight
-- name    : OAI.ShortEgyptian.rankin_divisor_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:42:28.009795+00:00
-- url     : https://prove2.me/theorems/9e45b3d1-997f-40c4-9773-da3c9b21e5c1
-- title:
--   Rankin's trick for $\sum\tau(d)^r/d$ over large integers with prime factors in $P$
-- statement:
--   For a positive integer $d$ let $\tau(d)$ be the number of its positive divisors, and for an integer $r\ge0$ let $C_r=\sum_{j\ge0}(j+2)^r(3/4)^j$. Let $A>0$ and $0\le\lambda\le\frac12$ be real numbers, let $P$ be a finite set of natural numbers, and let $s$ be a finite set of positive integers $d$ such that every prime factor of $d$ belongs to $P$ and $d\ge A$. Then
--
--   $$
--   \sum_{d\in s}\frac{\tau(d)^r}{d}\;\le\;\exp\Bigl(-\lambda\log A+C_r\sum_{\substack{p\in P\\ p\ \text{prime}}}p^{-(1-\lambda)}\Bigr).
--   $$
--
--   This is Rankin's trick for the harmonic sum of $\tau(d)^r$ over integers composed of primes from $P$: restricting to $d\ge A$ gains the factor $A^{-\lambda}=e^{-\lambda\log A}$, at the price of replacing $p^{-1}$ by the larger $p^{-(1-\lambda)}$ in the prime sum. Choosing $\lambda$ well shows that large integers with only prime factors from $P$ carry little of this weight.
--
--   **Formalization Note** The hypothesis is `d ∈ Nat.factoredNumbers P ∧ A ≤ d` (so $d\neq0$); the summand is `(d.divisors.card : ℝ) ^ r / d`, and $C_r$ is `momentSeriesConst r`. Non-prime elements of $P$ are ignored on the right-hand side.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean#L126-L153

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

theorem OAI.ShortEgyptian.rankin_divisor_weight (r : ℕ) (A lam : ℝ) (hA : 0 < A)
    (hlam : 0 ≤ lam) (hlamsmall : lam ≤ 1/2) (s P : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P ∧ A ≤ d) :
    ∑ d ∈ s, (d.divisors.card : ℝ)^r / d ≤
      Real.exp (-lam * Real.log A + momentSeriesConst r *
        ∑ p ∈ P with p.Prime, (p:ℝ)^(-(1-lam))) := by sorry
