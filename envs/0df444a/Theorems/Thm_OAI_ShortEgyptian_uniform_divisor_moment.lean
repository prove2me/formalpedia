-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_uniform_divisor_moment
-- name    : OAI.ShortEgyptian.uniform_divisor_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:54:43.02383+00:00
-- url     : https://prove2.me/theorems/a8401c31-d417-4ee9-93ff-bee220281391
-- title:
--   Uniform short-interval moment bound for truncated divisor counts at all large scales
-- statement:
--   For $X\in\mathbb{R}$ and $n\in\mathbb{N}$ let $\tau_X(n)$ be the number of divisors $a$ of $n$ with $a\le X$. Fix a real number $D\ge 1$ and $r\in\mathbb{N}$. Then for all sufficiently large real $S$ the following holds. For all real $v,Y$ and all $N\in\mathbb{N}$ with
--   $$\frac{S}{2\log S}\le v\le DS,\qquad e^{v/2}\le Y\le e^{v},\qquad N\le e^{DS},$$
--   one has
--
--   $$
--   \sum_{N<n\le N+\lfloor Y\rfloor}\tau_{e^{v}}(n)^r\;\le\;Y\exp\big(S^{1/4}\big).
--   $$
--
--   The threshold for $S$ depends only on $D$ and $r$, and the bound is uniform in $v$, $Y$ and $N$ in the stated ranges.
--
--   This is the asymptotic form of the moment estimate for divisor counts truncated at $e^{v}$. On every interval of length $\lfloor Y\rfloor$ whose left end lies below $e^{DS}$, the average of $\tau_{e^{v}}(n)^r$ is at most $e^{S^{1/4}}$. Since $v\ge S/(2\log S)$, this factor is $e^{o(v)}$ as $S\to\infty$.
--
--   **Formalization Note** "For all sufficiently large $S$" is the filter statement `∀ᶠ S : ℝ in atTop`. In Lean, $\tau_X(n)$ is `truncatedDivisorCount X n`, and the interval is `Ioc N (N + ⌊Y⌋₊)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean#L247-L268

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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
open Filter Topology Asymptotics

theorem OAI.ShortEgyptian.uniform_divisor_moment (D : ℝ) (hD : 1 ≤ D) (r : ℕ) :
    ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N : ℕ),
      S/(2*Real.log S) ≤ v → v ≤ D*S → Real.exp (v/2) ≤ Y → Y ≤ Real.exp v →
      (N:ℝ) ≤ Real.exp (D*S) →
      ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ Y*Real.exp (S^(1/4:ℝ)) := by sorry
