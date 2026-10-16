-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_moment_band_nonpos
-- name    : OAI.ShortEgyptian.moment_band_nonpos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:51:35.946996+00:00
-- url     : https://prove2.me/theorems/2edf2136-cfb7-45e8-a574-efa744e79545
-- title:
--   Nonpositivity of the band exponent in the divisor-moment estimate
-- statement:
--   For $r\in\mathbb{N}$ let $C_r=\sum_{j\ge0}(j+2)^r(3/4)^j$, and for $T>1$ let $H(T)=8+4\log\big(1+\log T/\log 2\big)$. For real $v,W$ and $t>0$ put $B=\big(1+\log(W/v)\big)v$, $\lambda_t=\dfrac{\log(v/t)}{10t}$ and
--   $E_t=\dfrac{rB}{t}-\dfrac{\lambda_t v}{5}+C_r\,(e^{2t})^{\lambda_t}H(e^{2t})$.
--
--   Let $r\in\mathbb{N}$ and let $S,v,W,t$ be real numbers with $S>1$, $t>0$, $v>0$, such that
--
--   1. $2\log S\le t\le S$;
--   2. $r\big(1+\log(W/v)\big)\le\dfrac{\log S}{3200}$;
--   3. $S^{1/16}\le v/t\le S^{2}$;
--   4. $C_r\,H(e^{2S})\le\dfrac{S^{1/20}\log S}{3200}$.
--
--   Then
--
--   $$
--   0\le\lambda_t\le\tfrac12\qquad\text{and}\qquad E_t\le 0.
--   $$
--
--   In the divisor-cover estimate for moments of truncated divisor counts, $E_t$ is the exponent of the total mass contributed by integers whose splitting prime $p$ has $\log p\approx t$, and $\lambda_t$ is the Rankin exponent used there. The lemma shows, from conditions on a single scale parameter $S$, that every such band contributes mass at most $e^{E_t}\le 1$.
--
--   **Formalization Note** In Lean, $E_t$ is `momentBandExp r v W t`, $B$ is `momentB v W`, $C_r$ is `momentSeriesConst r` and $H$ is `primeRecipBound`; $(e^{2t})^{\lambda_t}$ and $S^{1/16}$, $S^{1/20}$ are real powers. The hypothesis $t>0$ is listed separately, although it follows from $2\log S\le t$ and $S>1$. No relation between $v$ and $W$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/MomentDecay.lean#L20-L84

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

theorem OAI.ShortEgyptian.moment_band_nonpos (r : ℕ) (S v W t : ℝ)
    (hS : 1 < S) (ht : 0 < t) (hv : 0 < v) (htlo : 2*Real.log S ≤ t)
    (htup : t ≤ S) (hB : (r:ℝ)*(1+Real.log (W/v)) ≤ Real.log S/3200)
    (hQlo : S^(1/16:ℝ) ≤ v/t) (hQup : v/t ≤ S^2)
    (hC : momentSeriesConst r*primeRecipBound (Real.exp (2*S)) ≤ S^(1/20:ℝ)*Real.log S/3200) :
    0 ≤ Real.log (v/t)/(10*t) ∧ Real.log (v/t)/(10*t) ≤ 1/2 ∧ momentBandExp r v W t ≤ 0 := by sorry
