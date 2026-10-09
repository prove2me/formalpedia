-- Prove2me | Theorems.Thm_Helfgott_odd_floor_two_power_sum_upper
-- name    : Helfgott.odd_floor_two_power_sum_upper
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T05:25:06.465071+00:00
-- url     : https://prove2.me/theorems/6bd7e5c3-42ea-4d21-bb8a-723c70fcf509
-- title:
--   Explicit odd floor-dependent two-power sums for Vaughan energy
-- statement:
--   Let $U\ge0$, $A,Y\ge1$ be integers and $L,T\ge0$ real numbers. Let $\alpha,\beta\ge0$ with $0<\alpha+\beta\le1$, and define
--   $$N_k=\max\left(1,\left\lfloor\frac A{(U+1)k}\right\rfloor\right),\qquad\Psi_\gamma(Y)=1+\frac{Y^\gamma-1}{2\gamma}.$$
--   Then
--   $$\sum_{\substack{1\le k\le Y\\k\ {\rm odd}}}\frac{(L/N_k)^\alpha(T/N_k)^\beta}k\le\left(\frac{2L(U+1)}A\right)^\alpha\left(\frac{2T(U+1)}A\right)^\beta\Psi_{\alpha+\beta}(Y).$$
--   This explicitly evaluates the floor-dependent power sums in the sharp two-power Vaughan coefficient-energy bound, retaining the factor one-half from restricting the sum to odd indices.
-- source:
--   Exact natural quotient comparison and decreasing odd-step integral bound toward Helfgott Type II coefficient-energy estimates. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott
theorem odd_floor_two_power_sum_upper (U A Y : ℕ) (L T alpha beta : ℝ)
    (hA : 1 ≤ A) (hY : 1 ≤ Y) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ alpha) (hb : 0 ≤ beta) (hab0 : 0 < alpha+beta) (hab1 : alpha+beta ≤ 1) :
    (∑ k∈Icc 1 Y,if Nat.Coprime k 2 then
      (L/(max 1 (A/((U+1)*k)) : ℕ))^alpha*
        (T/(max 1 (A/((U+1)*k)) : ℕ))^beta/k else 0) ≤
      (2*L*(U+1 : ℕ)/A)^alpha*(2*T*(U+1 : ℕ)/A)^beta*
        (1+((Y : ℝ)^(alpha+beta)-1)/(2*(alpha+beta))) := by sorry
end Helfgott
