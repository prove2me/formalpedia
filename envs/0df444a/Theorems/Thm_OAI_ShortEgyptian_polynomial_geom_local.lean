-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_polynomial_geom_local
-- name    : OAI.ShortEgyptian.polynomial_geom_local
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:39:57.61061+00:00
-- url     : https://prove2.me/theorems/ccf40d1f-de38-460a-b9ac-e933bfb5f3a1
-- title:
--   Exponential bound for the series $\sum_{j\ge0}(j+1)^r x^j$ on $0\le x\le 3/4$
-- statement:
--   For an integer $r\ge0$ let
--   $$C_r=\sum_{j=0}^{\infty}(j+2)^r\Bigl(\frac34\Bigr)^j ,$$
--   a finite positive constant (the series converges since its ratio tends to $3/4$). Let $0\le x\le 3/4$ be a real number. Then:
--
--   1. the series $\sum_{j\ge0}(j+1)^r x^j$ converges;
--   2. its sum is bounded by an exponential that is linear in $x$:
--
--   $$
--   \sum_{j=0}^{\infty}(j+1)^r x^j\;\le\;\exp\bigl(C_r\,x\bigr).
--   $$
--
--   The series is the local Euler factor of a divisor-type weight: if $\tau(n)$ is the number of divisors of $n$ and $x=p^{-\sigma}$ for a prime $p$, then $\sum_j\tau(p^j)^r p^{-j\sigma}=\sum_j(j+1)^rx^j$. The bound $1+O(x)\le\exp(C_rx)$ lets one turn products of such factors over primes into exponentials of sums over primes.
--
--   **Formalization Note** $C_r$ is `momentSeriesConst r`, defined as a `tsum`; part 1 is stated as `Summable`, and the sum in part 2 is the corresponding `tsum`. For $x=0$ the convention $0^0=1$ applies, and both sides equal $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean#L24-L47

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

theorem OAI.ShortEgyptian.polynomial_geom_local (r : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 3/4) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ)^r * x^j) ∧
    (∑' j : ℕ, ((j + 1 : ℕ) : ℝ)^r * x^j) ≤ Real.exp (momentSeriesConst r * x) := by sorry
