-- Prove2me | Theorems.Thm_JRPHard_RangeDiv_f_at_L_U
-- name    : JRPHard.RangeDiv.f_at_L_U
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:12.262225+00:00
-- url     : https://prove2.me/theorems/05f51c73-ba2c-4755-b7e5-53817cc312d2
-- title:
--   Proof of Lemma 3, p. 14 — f(q) = LU/q + q bounds the objective of (5) below, f(L) = f(U) = L + U, and f is minimized at √(LU)
-- statement:
--   Let $M \ge U \ge L > 0$ be integers with $L + U < 2\sqrt{2LU}$, and let $f(x) = LU/x + x$ for real $x > 0$. Then:
--
--   1. for every positive integer $q$, $f(q) \le \dfrac{LU}{\gcd(q,M)} + q$;
--   2. $f(L) = f(U) = L + U$;
--   3. $f$ is minimized at $\sqrt{LU}$: for every real $x > 0$,
--   $$f\big(\sqrt{LU}\big) \le f(x).$$
--
--   The function $f$ coincides with the objective of problem (5) at divisors of $M$ and lies below it everywhere. It meets the level $L + U$ exactly at the two ends of the interval $[L, U]$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 14, §3.1, proof of Lemma 3, "The convex function f(q) ≡ K₀/q + q"

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting

namespace JRPHard.RangeDiv

theorem f_at_L_U (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) :
    (∀ q : ℕ, 0 < q → fConv L U q ≤ obj5 M L U q) ∧
    fConv L U L = L + U ∧ fConv L U U = L + U ∧
    (∀ x : ℝ, 0 < x → fConv L U (Real.sqrt ((L : ℝ) * U)) ≤ fConv L U x) := by sorry

end JRPHard.RangeDiv
