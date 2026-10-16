-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_order
-- name    : OAI.ShortEgyptian.reciprocal_phase_order
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:27:48.898921+00:00
-- url     : https://prove2.me/theorems/158c85a3-e1e4-4a59-8071-a0d05e3172e8
-- title:
--   Bound $8U/T$ for exponential sums of $Z/n$ when $Z^2$ lies between $U^{2r+3}$ and $U^{2r+5}$
-- statement:
--   Write $e(x)=e^{2\pi i x}$. For $r\in\mathbb{N}$ define the natural numbers
--   $$
--   C_r=\bigl(18\cdot3^{r+3}\bigr)^4\,\bigl((r+2)!\bigr)^2\,2^{2r},\qquad P_r=2^r(2r+4).
--   $$
--   Let $r\in\mathbb{N}$, $T,U,Z\in\mathbb{R}$ and $p,q\in\mathbb{Z}$ with
--   $$
--   T\ge1,\quad C_r\,T^{P_r}\le U,\quad Z\ge0,\quad U^{2r+3}\le Z^2\le U^{2r+5},\quad U\le p,\quad q\le2U .
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\Bigl(\frac Zn\Bigr)\Bigr|\le\frac{8U}{T}.
--   $$
--
--   Thus, on a range $[p,q]\subseteq[U,2U]$ with $U$ at least a fixed power of $T$, the exponential sum of the reciprocal phase $Z/n$ is smaller than the trivial bound by a factor of order $T$, provided $Z$ lies in the window $U^{r+3/2}\le Z\le U^{r+5/2}$. The index $r$ is matched to the size of $Z$ relative to $U$; letting $r$ run through $0,1,2,\dots$ covers all $Z\ge U^{3/2}$ when $U\ge1$, with constants depending on $r$.
--
--   **Formalization Note** $C_r$ is `reciprocalConstantNat r` and $P_r$ is `reciprocalPower r`, both natural numbers cast to reals. $Z/n$ is real division by the integer $n$ cast to a real, with $n\ge p\ge U>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean#L92-L161

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

theorem OAI.ShortEgyptian.reciprocal_phase_order (r : ℕ) (T U Z : ℝ) (p q : ℤ)
    (hT : 1 ≤ T) (hlarge : (reciprocalConstantNat r : ℝ) * T ^ reciprocalPower r ≤ U)
    (hZ : 0 ≤ Z) (hZlo : U ^ (2 * r + 3) ≤ Z ^ 2)
    (hZhi : Z ^ 2 ≤ U ^ (2 * r + 5))
    (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U / T := by sorry
