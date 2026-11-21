-- Prove2me | Theorems.Thm_MasulloGRH_exists_tendsto_atTop_summable_mul
-- name    : MasulloGRH.exists_tendsto_atTop_summable_mul
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-21T00:26:08.650745+00:00
-- url     : https://prove2.me/theorems/c33515ab-6457-43fa-b256-f367b5c8f342
-- title:
--   Summable weights admit an unbounded summable rescaling
-- statement:
--   Let $(c_n)$ be a summable sequence of nonnegative reals. Then there is a sequence $\mu_n\ge 1$ with $\mu_n\to\infty$ such that $\sum_n c_n\mu_n<\infty$.
--
--   (Classical: with tails $r_n=\sum_{k\ge n}c_k$ one may take e.g. $\mu_n$ growing slowly along blocks where $r_n\le 4^{-j}$, $\mu_n=2^j$.)
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C — auxiliary step in the proof that a weak expansion yields a scalar (nuclear) expansion

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem exists_tendsto_atTop_summable_mul (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c) :
    ∃ μ : ℕ → ℝ, (∀ n, 1 ≤ μ n) ∧ Filter.Tendsto μ Filter.atTop Filter.atTop ∧
      Summable (fun n => c n * μ n) := by sorry

end MasulloGRH
