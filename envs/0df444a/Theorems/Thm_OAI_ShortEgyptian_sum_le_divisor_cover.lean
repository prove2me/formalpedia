-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_sum_le_divisor_cover
-- name    : OAI.ShortEgyptian.sum_le_divisor_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:48:16.722728+00:00
-- url     : https://prove2.me/theorems/ccb62497-17ce-4c92-a7c3-0581f3e9afa9
-- title:
--   Bounding a short-interval sum by a weighted cover of divisors
-- statement:
--   Let $I$ be a finite index set; for each $i\in I$ let $D_i$ be a finite set of natural numbers, and let $F(i,d)$ be real weights. Let $N\in\mathbb{N}$, let $Y\ge 0$ be a real number, and let $w:\mathbb{N}\to\mathbb{R}$ be an arbitrary function. Write
--   $J=\{n\in\mathbb{N}: N<n\le N+\lfloor Y\rfloor\}$
--   for the integers in the interval of length $\lfloor Y\rfloor$ that starts after $N$. Assume:
--
--   1. $F(i,d)\ge 0$ for all $i\in I$ and $d\in D_i$;
--   2. $0<d\le Y$ for all $i\in I$ and $d\in D_i$;
--   3. (covering) for every $n\in J$ there are $i\in I$ and $d\in D_i$ with $d\mid n$ and $w(n)\le F(i,d)$.
--
--   Then
--
--   $$
--   \sum_{n\in J} w(n)\;\le\;2Y\sum_{i\in I}\sum_{d\in D_i}\frac{F(i,d)}{d}.
--   $$
--
--   This is a divisor-cover principle. If every integer of a short interval is dominated by the weight of one of its divisors from a prescribed family, then the total is controlled by the harmonic-type masses $\sum_{d}F(i,d)/d$, because an interval of length $\lfloor Y\rfloor$ contains at most $2Y/d$ multiples of any $d\le Y$. It converts pointwise bounds for $w(n)$ into averaged bounds over short intervals, and it is used to estimate moments of truncated divisor counts.
--
--   **Formalization Note** The index set is a `Finset` over an arbitrary type, the interval $J$ is `Ioc N (N + ⌊Y⌋₊)` with the natural-number floor, and $F(i,d)/d$ is real division (with $d>0$ by hypothesis 2). No sign condition on $w$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorCover.lean#L53-L93

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
universe uι
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.sum_le_divisor_cover {ι : Type uι} (I : Finset ι) (D : ι → Finset ℕ)
    (F : ι → ℕ → ℝ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) (w : ℕ → ℝ)
    (hF : ∀ i ∈ I, ∀ d ∈ D i, 0 ≤ F i d)
    (hD : ∀ i ∈ I, ∀ d ∈ D i, 0 < d ∧ (d:ℝ) ≤ Y)
    (hc : ∀ n ∈ Ioc N (N+⌊Y⌋₊), ∃ i ∈ I, ∃ d ∈ D i, d ∣ n ∧ w n ≤ F i d) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), w n ≤ 2*Y * ∑ i ∈ I, ∑ d ∈ D i, F i d/d := by sorry
