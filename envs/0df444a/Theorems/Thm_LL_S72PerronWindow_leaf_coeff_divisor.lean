-- Prove2me | Theorems.Thm_LL_S72PerronWindow_leaf_coeff_divisor
-- name    : LL_S72PerronWindow.leaf_coeff_divisor
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-25T13:06:32.458448+00:00
-- url     : https://prove2.me/theorems/7b1c19fc-6c79-4ed5-b893-911f2144ab8d
-- title:
--   Coefficients bounded by a power of the divisor function are $O(Y^{1/200})$ on $J$
-- statement:
--   Let $b:\mathbb R\times\mathbb N\to\mathbb R$, $\varepsilon>0$ and real $B$, and suppose there is $C_0$ with $|b(x,k)|\le C_0\,d(k)^B$ for all $x,k$, where $d(k)$ is the number of divisors and the power is the real power. Then there are $K\ge0$ and $C$ such that $|b(x,m)|\le K\,Y^{1/200}$ for all real $x\ge C$ and all $m\in J$, with $Y=x^{11/20+\varepsilon}$.
-- source:
--   Baker, Harman and Pintz 1997, display 3.1 and page 44.

import Mathlib
import Definitions.Def_LL_S72PerronWindow_rightInterval

open Classical Complex
open scoped BigOperators
open MeasureTheory

namespace LL_S72PerronWindow
theorem leaf_coeff_divisor (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m ∈ rightInterval ε x,
      |b x m| ≤ K * (x ^ (11 / 20 + ε)) ^ (1 / 200 : ℝ) := by sorry
end LL_S72PerronWindow
