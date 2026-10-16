-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_divisor_harmonic_bound
-- name    : OAI.ShortEgyptian.divisor_harmonic_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:06.604553+00:00
-- url     : https://prove2.me/theorems/a64fd5ef-f327-4434-acc4-2ad8173945e8
-- title:
--   Bound for $\sum_{d\le T}\tau(d)^r/d$ through a sum over prime reciprocals
-- statement:
--   For a positive integer $d$ let $\tau(d)$ be the number of positive divisors of $d$. For $r\in\mathbb{N}$ let $C_r=\sum_{j\ge 0}(j+2)^r(3/4)^j$ (a convergent series), and for real $T>1$ let
--   $H(T)=8+4\log\!\big(1+\tfrac{\log T}{\log 2}\big)$.
--   Then for every $r\in\mathbb{N}$ and every real $T\ge 2$,
--
--   $$
--   \sum_{d=1}^{\lfloor T\rfloor}\frac{\tau(d)^r}{d}\;\le\;\exp\big(C_r\,H(T)\big).
--   $$
--
--   Since $\exp(C_rH(T))=e^{8C_r}\,(1+\log_2 T)^{4C_r}$, the logarithmically weighted sum of $\tau(d)^r$ up to $T$ grows at most like a fixed power of $\log T$, with fully explicit constants.
--
--   In moment estimates for truncated divisor counts over short intervals, this bound controls the contribution of the integers that are covered by a divisor $d$ below the square root of the interval length.
--
--   **Formalization Note** In Lean, $\tau(d)$ is `d.divisors.card`, $C_r$ is `momentSeriesConst r` (defined as a `tsum`; the series converges), $H(T)$ is `primeRecipBound T`, and the summation range is `Icc 1 ⌊T⌋₊`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean#L74-L89

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

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.divisor_harmonic_bound (r : ℕ) (T : ℝ) (hT : 2 ≤ T) :
    ∑ d ∈ Icc 1 ⌊T⌋₊, (d.divisors.card:ℝ)^r/d ≤
      Real.exp (momentSeriesConst r * primeRecipBound T) := by sorry
