-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_power_bound
-- name    : OAI.ShortEgyptian.reciprocal_phase_power_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:29:10.417746+00:00
-- url     : https://prove2.me/theorems/e17e63eb-f7fe-4118-9023-c59f47301f6e
-- title:
--   Bound $8U/T$ for exponential sums of $Z/n$ on $[U,2U]$ uniformly for $U^4\le|Z|\le U^B$
-- statement:
--   Write $e(x)=e^{2\pi i x}$. For $r\in\mathbb{N}$ let
--   $$
--   C_r=\bigl(18\cdot3^{r+3}\bigr)^4\,\bigl((r+2)!\bigr)^2\,2^{2r},\qquad P_r=2^r(2r+4).
--   $$
--   Let $B\in\mathbb{N}$ with $B\ge4$, let $T,U,Z\in\mathbb{R}$ and $p,q\in\mathbb{Z}$, and assume
--   $$
--   T\ge1,\quad C_B\,T^{P_B}\le U,\quad U^4\le|Z|\le U^B,\quad U\le p,\quad q\le2U .
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\Bigl(\frac Zn\Bigr)\Bigr|\le\frac{8U}{T}.
--   $$
--
--   Thus, once $U$ exceeds a fixed power of $T$ depending only on $B$, the exponential sum of the reciprocal phase $Z/n$ over $n\in[p,q]\subseteq[U,2U]$ is smaller than the trivial bound by a factor of order $T$. This holds uniformly for all real frequencies $Z$, of either sign, with $U^4\le|Z|\le U^B$. Such bounds control the distribution modulo $1$ of the numbers $Z/n$; in this development they are combined over dyadic blocks to treat longer ranges of $n$.
--
--   **Formalization Note** $C_r$ is `reciprocalConstantNat r` and $P_r$ is `reciprocalPower r`. $Z/n$ is real division by the integer $n$ cast to a real, with $n\ge p\ge U\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean#L173-L210

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.reciprocal_phase_power_bound (B : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hB : 4 ≤ B) (hT : 1 ≤ T)
    (hlarge : (reciprocalConstantNat B : ℝ) * T ^ reciprocalPower B ≤ U)
    (hZlo : U ^ 4 ≤ |Z|) (hZhi : |Z| ≤ U ^ B)
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by sorry
