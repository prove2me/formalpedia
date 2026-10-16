-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_long_interval
-- name    : OAI.ShortEgyptian.reciprocal_phase_long_interval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:37:04.737896+00:00
-- url     : https://prove2.me/theorems/71e4f244-04fd-49e7-a7ba-0e15cc982fca
-- title:
--   Cancellation in the reciprocal exponential sum $\sum_{p\le n\le q} e(Z/n)$ over a long interval
-- statement:
--   Write $e(x)=\exp(2\pi i x)$ for real $x$. For an integer $B\ge0$ define the constants
--   $$C_B=\bigl(18\cdot3^{B+3}\bigr)^4\,\bigl((B+2)!\bigr)^2\,2^{2B},\qquad P_B=2^B\,(2B+4).$$
--
--   Let $B\ge4$ be an integer, let $T\ge1$ and $Z$ be real numbers, and let $p\ge1$ and $q$ be natural numbers such that
--   $$C_B\,T^{P_B}\le p\qquad\text{and}\qquad q^4\le|Z|\le p^B .$$
--   Then
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\!\left(\frac{Z}{n}\right)\Bigr|\;\le\;\frac{16\,q}{T}.
--   $$
--
--   (If $q<p$ the sum is empty.) The trivial bound is the number of terms, at most $q$, so the theorem saves a factor $T/16$, provided the starting point $p$ is large in terms of $T$ and $|Z|$ lies between $q^4$ and $p^B$. The interval may be much longer than $p$: its length is limited only through $q\le p^{B/4}$, which is forced by $q^4\le|Z|\le p^B$. For an integer $Z$ the fractional part of $Z/n$ is $(Z\bmod n)/n$, so such sums measure how the residues of $Z$ modulo the integers $n\in[p,q]$ are distributed.
--
--   **Formalization Note** The constants are `reciprocalConstantNat B` and `reciprocalPower B`; $e(x)$ is `phase x`; the sum runs over `Finset.Icc p q` of natural numbers, with $Z/n$ computed in the reals (no division by zero occurs since $n\ge p\ge1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DeterministicMean.lean#L64-L84

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

open OAI OAI.ShortEgyptian
universe uα uβ
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.reciprocal_phase_long_interval (B : ℕ) (T Z : ℝ) (p q : ℕ)
    (hB : 4 ≤ B) (hT : 1 ≤ T) (hp : 1 ≤ p)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ p)
    (hZlo : (q : ℝ) ^ 4 ≤ |Z|) (hZhi : |Z| ≤ (p : ℝ) ^ B) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 16 * q / T := by sorry
