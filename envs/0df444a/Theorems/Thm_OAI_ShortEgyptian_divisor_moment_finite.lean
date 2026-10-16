-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_divisor_moment_finite
-- name    : OAI.ShortEgyptian.divisor_moment_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:50:53.785328+00:00
-- url     : https://prove2.me/theorems/fdd19f7d-9a95-4a48-85ae-e5dc8ed82421
-- title:
--   Short-interval moment bound for truncated divisor counts under explicit parameter conditions
-- statement:
--   **Notation.** For $X\in\mathbb{R}$ and $n\in\mathbb{N}$ let $\tau_X(n)$ be the number of divisors $a$ of $n$ with $a\le X$, and let $\tau(n)$ be the number of all divisors. Put
--   - $C_r=\sum_{j\ge0}(j+2)^r(3/4)^j$ for $r\in\mathbb{N}$, and $Z=\sum_{m\ge1}m^{-41/40}$;
--   - $H(T)=8+4\log\big(1+\log T/\log 2\big)$;
--   - $B=B(v,W)=\big(1+\log(W/v)\big)\,v$;
--   - $P=P(r,v,W,z)=r\big(z\log(1+W/\log 2)+B/\log z\big)$;
--   - for $t>0$: $\lambda_t=\dfrac{\log(v/t)}{10t}$ and $E_t=\dfrac{rB}{t}-\dfrac{\lambda_t v}{5}+C_r\,(e^{2t})^{\lambda_t}\,H(e^{2t})$.
--
--   Let $r,N\in\mathbb{N}$ and let $Y,v,W,z,T,L$ be real numbers such that
--
--   1. $Y\ge 4$, $0<v<W$, $z>1$ and $v/2\le\log Y$;
--   2. $0<L\le v/20$, $T>0$ and $\log T\ge 2$;
--   3. $\log n\le W$ for every integer $n$ with $N<n\le N+\lfloor Y\rfloor$;
--   4. $P-v/50+C_0\,T^{1/8}Z\le 0$;
--   5. for every real $t$ with $t\ge 1$, $\tfrac12\log T\le t$ and $t\le L$: $\ 0\le\lambda_t\le\tfrac12$ and $E_t\le 0$.
--
--   Then
--
--   $$
--   \sum_{N<n\le N+\lfloor Y\rfloor}\tau_{e^{v}}(n)^r\;\le\;2Y\Big(\exp\Big(\frac{rB}{L}+C_r\,H(\sqrt{Y})\Big)+\lfloor L\rfloor+1\Big).
--   $$
--
--   This is the main structural step in bounding moments of the number of divisors below $e^{v}$ over a short interval of length $\lfloor Y\rfloor$. Conditions 4 and 5 are purely numerical. They are checked separately once $W$, $z$, $T$ and $L$ are chosen as functions of a single scale parameter, and the bound then becomes a clean estimate in that parameter.
--
--   **Formalization Note** In Lean, $\tau_X(n)$ is `truncatedDivisorCount X n`, and $C_r$, $Z$, $H$, $B$, $P$, $E_t$ are `momentSeriesConst r`, `smallSmoothConst`, `primeRecipBound`, `momentB v W`, `momentPoint r v W z` and `momentBandExp r v W t`. The series $Z$ is written as a sum over all $m\ge 0$, with the real-power convention $0^{-41/40}=0$. The interval is `Ioc N (N + ⌊Y⌋₊)`, and $T^{1/8}$, $(e^{2t})^{\lambda_t}$ are real powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/DivisorMoments.lean#L46-L204

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

theorem OAI.ShortEgyptian.divisor_moment_finite (r : ℕ) (N : ℕ) (Y v W z T L : ℝ)
    (hY : 4 ≤ Y) (hv : 0 < v) (hvW : v < W) (hz : 1 < z)
    (hYv : v/2 ≤ Real.log Y) (hL : 0 < L) (hLv : L ≤ v/20)
    (hT : 2 ≤ Real.log T) (hTpos : 0 < T)
    (hnW : ∀ n ∈ Ioc N (N+⌊Y⌋₊), Real.log n ≤ W)
    (hsmall : momentPoint r v W z -v/50 + momentSeriesConst 0*(T^(1/8:ℝ)*smallSmoothConst) ≤ 0)
    (hband : ∀ t : ℝ, 1 ≤ t → Real.log T/2 ≤ t → t ≤ L →
      0 ≤ Real.log (v/t)/(10*t) ∧ Real.log (v/t)/(10*t) ≤ 1/2 ∧ momentBandExp r v W t ≤ 0) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤
      2*Y*(Real.exp ((r:ℝ)*momentB v W/L + momentSeriesConst r*primeRecipBound (Real.sqrt Y)) +
        (⌊L⌋₊:ℝ)+1) := by sorry
