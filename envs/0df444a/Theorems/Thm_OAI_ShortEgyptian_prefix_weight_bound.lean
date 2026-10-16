-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_prefix_weight_bound
-- name    : OAI.ShortEgyptian.prefix_weight_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:49:53.185964+00:00
-- url     : https://prove2.me/theorems/2925d6a8-2f20-4002-83f0-a9888b582360
-- title:
--   Truncated divisor count of $n=de$ when the cofactor $e$ has only large prime factors
-- statement:
--   For a real number $X$ and a natural number $m$ let $\tau_X(m)=\#\{a\in\mathbb{N}: a\mid m,\ a\le X\}$ be the number of divisors of $m$ not exceeding $X$, and let $\tau(m)$ be the number of all divisors of $m$.
--
--   Let $n,d,e\in\mathbb{N}$ with $n=de$, $d\ne 0$ and $e\ne 0$; let $p$ be a prime such that every prime factor of $e$ is at least $p$; let $r\in\mathbb{N}$; and let $v,W$ be real numbers with $0<v<W$ and $\log n\le W$. Then
--
--   $$
--   \tau_{e^{v}}(n)^r\;\le\;\tau(d)^r\,\exp\!\Big(\frac{r\,\big(1+\log(W/v)\big)\,v}{\log p}\Big).
--   $$
--
--   So the number of divisors of $n$ below $e^{v}$ is controlled by the full divisor count of the part $d$ times a factor that is close to $1$ when the cofactor $e$ is very rough, that is, when $\log p$ is large compared with $v\,(1+\log(W/v))$. Together with a splitting $n=de$ of $n$ at a threshold along its prime factorization, it bounds truncated divisor counts in moment estimates over short intervals.
--
--   **Formalization Note** $\tau_X(m)$ is `truncatedDivisorCount X m` and $\tau(d)$ is `d.divisors.card`. The prime $p$ is not required to divide $e$; the hypothesis on $e$ is that every element of `e.primeFactorsList` is at least $p$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/SmoothBounds.lean#L107-L126

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

theorem OAI.ShortEgyptian.prefix_weight_bound {n d e p : ℕ} (hde : n = d*e)
    (hd : d ≠ 0) (he : e ≠ 0) (hp : p.Prime) (r : ℕ) (v W : ℝ)
    (hv : 0 < v) (hvW : v < W) (hnW : Real.log n ≤ W)
    (hr : ∀ q ∈ e.primeFactorsList, p ≤ q) :
    (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ (d.divisors.card:ℝ)^r *
      Real.exp ((r:ℝ)*(1+Real.log (W/v))*v/Real.log p) := by sorry
