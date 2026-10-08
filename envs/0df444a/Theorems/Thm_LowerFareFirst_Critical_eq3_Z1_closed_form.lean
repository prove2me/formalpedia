-- Prove2me | Theorems.Thm_LowerFareFirst_Critical_eq3_Z1_closed_form
-- name    : LowerFareFirst.Critical.eq3_Z1_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:21.971864+00:00
-- url     : https://prove2.me/theorems/1a7ce6ac-46f0-40cc-801a-98b6dec0c399
-- title:
--   Eq. (3), p. 28 — Z_1(n) = r_1{nP[D_1 ≥ n] + Σ_{j<n} jP[D_1 = j]}
-- statement:
--   Consider the seat management model with lower fare classes booking first: fare classes $1, \dots, c$ with fares $r_1 > \cdots > r_c > 0$, integer-valued demands $D_m$ on a probability space, and $Z_m(n)$ the optimal expected revenue with $n$ empty seats when only classes $1, \dots, m$ may book, under the standing assumptions of §1.
--
--   When only the highest class may book, the optimal expected revenue is given in closed form: for every $n \ge 0$,
--   $$Z_1(n) = r_1 \Big\{ n\,P[D_1 \ge n] + \sum_{j=0}^{n-1} j\,P[D_1 = j] \Big\}.$$
--
--   The right-hand side is $r_1 \mathbb E[\min(D_1, n)]$: with a single class every request is accepted while seats remain. Equation (3) is the base case of the paper's induction and yields the marginal seat value (4).
-- source:
--   Wollmer (1992), Operations Research 40(1), §2, Eq. (3), p. 28

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

namespace LowerFareFirst.Critical

open MeasureTheory

theorem eq3_Z1_closed_form {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (c : ℕ)
    (hM : IsSeatModel μ D r c) :
    ∀ n : ℕ, Z μ D r 1 n =
      r 1 * ((n : ℝ) * probGe μ D 1 n + ∑ j ∈ Finset.range n, (j : ℝ) * probEq μ D 1 j) := by sorry

end LowerFareFirst.Critical
