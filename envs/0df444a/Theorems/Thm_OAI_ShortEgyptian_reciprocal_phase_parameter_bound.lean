-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_phase_parameter_bound
-- name    : OAI.ShortEgyptian.reciprocal_phase_parameter_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:26:42.37675+00:00
-- url     : https://prove2.me/theorems/d0a98b3a-3f7f-4e5f-adce-68623fd779ff
-- title:
--   Bound $8U\varepsilon$ for exponential sums of $Z/n$ on $[U,2U]$ under explicit parameter conditions
-- statement:
--   Write $e(x)=e^{2\pi i x}$. Let $r,L\in\mathbb{N}$, $Z,U,\varepsilon\in\mathbb{R}$ and $p,q\in\mathbb{Z}$. Put $\delta=\varepsilon^{2^r}$ and
--   $$
--   c=Z\,(r+2)!\,\Bigl(\frac1{3U}\Bigr)^{r+3}.
--   $$
--   Assume that $L\ge1$, $U\ge1$, $L\le2U$, $Z\ge0$, $U\le p$, $q\le2U$, $0<\varepsilon\le1$ and $1/L\le\delta$, and that the following size conditions hold:
--   $$
--   U\delta\ge18,\qquad\Bigl(\frac{18}{U\delta}\Bigr)^2\le c,\qquad L^r\,c\le\Bigl(\frac{\delta}{18\cdot3^{r+3}}\Bigr)^2 .
--   $$
--   Then
--
--   $$
--   \Bigl|\sum_{n=p}^{q}e\Bigl(\frac Zn\Bigr)\Bigr|\le8U\varepsilon
--   $$
--
--   (the sum is empty if $q<p$).
--
--   The interval $[p,q]$ lies in $[U,2U]$ and has at most $U+1$ terms, so this saves the factor $\varepsilon$ over the trivial bound, up to the constant $8$. The conditions require $c$ to be neither too small nor, even after multiplication by $L^r$, too large. This is the core estimate behind the bounds for sums of $e(Z/n)$ in which $\varepsilon$, $L$ and $r$ are chosen in terms of a saving parameter and of the size of $Z$.
--
--   **Formalization Note** $Z/n$ is real division by the integer $n$ cast to a real; it is never a division by zero, since $n\ge p\ge U\ge1$. The condition $1/L\le\delta$ is `1 / (L : ℝ) ≤ eps ^ (2 ^ r)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ReciprocalEstimates.lean#L96-L186

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.reciprocal_phase_parameter_bound (r L : ℕ) (Z U eps : ℝ) (p q : ℤ)
    (hL : 1 ≤ L) (hU : 1 ≤ U) (hLU : (L : ℝ) ≤ 2 * U)
    (hZ : 0 ≤ Z) (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ r))
    (hconstant : 18 ≤ U * eps ^ (2 ^ r))
    (hlow : (18 / (U * eps ^ (2 ^ r))) ^ 2 ≤
      Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)))
    (hupp : (L : ℝ) ^ r *
      (Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))) ≤
      (eps ^ (2 ^ r) / (18 * (3 : ℝ) ^ (r + 3))) ^ 2) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U * eps := by sorry
