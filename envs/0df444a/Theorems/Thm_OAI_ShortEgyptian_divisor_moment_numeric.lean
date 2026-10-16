-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_divisor_moment_numeric
-- name    : OAI.ShortEgyptian.divisor_moment_numeric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:53:19.810974+00:00
-- url     : https://prove2.me/theorems/68fae32e-a361-4bf5-8352-1886614195ca
-- title:
--   Numerically explicit short-interval moment bound for truncated divisor counts
-- statement:
--   For $X\in\mathbb{R}$ and $n\in\mathbb{N}$ let $\tau_X(n)$ be the number of divisors $a$ of $n$ with $a\le X$. For $r\in\mathbb{N}$ let $C_r=\sum_{j\ge0}(j+2)^r(3/4)^j$, and let $Z=\sum_{m\ge1}m^{-41/40}$.
--
--   Let $r,N\in\mathbb{N}$ and let $D,S,v,Y$ be real numbers. Assume the following conditions on the scale $S$:
--
--   1. $1\le D\le S$, $S>1$ and $\log S\ge 1$;
--   2. $\log\big(1+\frac{D+1}{\log 2}\big)\le\log S$ and $\log\big(1+\frac{2}{\log 2}\big)\le\log S$;
--   3. $40\,(1+\log S)\le S^{1/16}$;
--   4. $1600\,r\,(1+\log S)^2\le S^{1/2}$;
--   5. $400\,C_0Z\,(1+\log S)\le S^{1/2}$;
--   6. $51200\,C_r\le S^{1/20}$;
--   7. $3200\,r\,\big(1+\log(2(D+1)\log S)\big)\le\log S$ and $1+\log\big(2(D+1)\log S\big)\le\log S$;
--   8. $8\,r\,D\,(1+\log S)\le S^{1/8}$;
--   9. $128\,C_r\,(1+\log S)\le S^{1/4}$ and $4\,(1+\log S)\le S^{1/4}$;
--
--   and the following conditions on $v$, $Y$ and $N$:
--
--   10. $\dfrac{S}{2\log S}\le v\le DS$;
--   11. $e^{v/2}\le Y\le e^{v}$;
--   12. $N\le e^{DS}$.
--
--   Then
--
--   $$
--   \sum_{N<n\le N+\lfloor Y\rfloor}\tau_{e^{v}}(n)^r\;\le\;Y\exp\big(S^{1/4}\big).
--   $$
--
--   Conditions 1 to 9 involve only $S$ and the fixed parameters $r$ and $D$, and each of them holds for all sufficiently large $S$. The theorem therefore says that, over any interval of length $\lfloor Y\rfloor$ with $e^{v/2}\le Y\le e^{v}$ starting below $e^{DS}$, the average of $\tau_{e^{v}}(n)^r$ is at most $e^{S^{1/4}}$. This is the explicit form of the asymptotic short-interval moment bound for divisor counts truncated at $e^{v}$.
--
--   **Formalization Note** In Lean, $\tau_X(n)$ is `truncatedDivisorCount X n`, $C_r$ is `momentSeriesConst r`, and $Z$ is `smallSmoothConst`, written as a sum over $m\ge 0$ with the real-power convention $0^{-41/40}=0$. The interval is `Ioc N (N + ⌊Y⌋₊)`, and all fractional powers are real powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean#L63-L245

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

theorem OAI.ShortEgyptian.divisor_moment_numeric (r : ℕ) (D S v Y : ℝ) (N : ℕ)
    (hD : 1 ≤ D) (hS : 1 < S) (hl : 1 ≤ Real.log S) (hDS : D ≤ S)
    (hElog : Real.log (1+(D+1)/Real.log 2) ≤ Real.log S)
    (h2log : Real.log (1+2/Real.log 2) ≤ Real.log S)
    (h40 : 40*(1+Real.log S) ≤ S^(1/16:ℝ))
    (hpoint : 1600*(r:ℝ)*(1+Real.log S)^2 ≤ S^(1/2:ℝ))
    (hsmall : 400*(momentSeriesConst 0*smallSmoothConst)*(1+Real.log S) ≤ S^(1/2:ℝ))
    (hband : 51200*momentSeriesConst r ≤ S^(1/20:ℝ))
    (hB : 3200*(r:ℝ)*(1+Real.log (2*(D+1)*Real.log S)) ≤ Real.log S)
    (hB1 : 1+Real.log (2*(D+1)*Real.log S) ≤ Real.log S)
    (hbig : 8*(r:ℝ)*D*(1+Real.log S) ≤ S^(1/8:ℝ))
    (hpr : 128*momentSeriesConst r*(1+Real.log S) ≤ S^(1/4:ℝ))
    (hout : 4*(1+Real.log S) ≤ S^(1/4:ℝ))
    (hvlo : S/(2*Real.log S) ≤ v) (hvup : v ≤ D*S)
    (hYlo : Real.exp (v/2) ≤ Y) (hYup : Y ≤ Real.exp v) (hN : (N:ℝ) ≤ Real.exp (D*S)) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ Y*Real.exp (S^(1/4:ℝ)) := by sorry
