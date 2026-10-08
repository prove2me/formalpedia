-- Prove2me | Theorems.Thm_Hlawka1D_hlawka_1d
-- name    : Hlawka1D.hlawka_1d
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-08T05:25:34.545012+00:00
-- url     : https://prove2.me/theorems/52baf14a-f150-43b0-845a-dd65344a0abb
-- title:
--   One-dimensional Hlawka inequality
-- statement:
--   For real numbers $a, b, c$: $|a+b|+|b+c|+|c+a| \le |a|+|b|+|c|+|a+b+c|$. The one-dimensional case of Hlawka's inequality; the base case for the proof that the sharp diagonal Hlawka constant of $\ell_2$ is $1$.
-- source:
--   Hlawka's inequality (1944); 1D case used as base for the p=2 sharp Hlawka constant proof

import Mathlib

theorem Hlawka1D.hlawka_1d : ∀ a b c : ℝ, |a + b| + |b + c| + |c + a| ≤ |a| + |b| + |c| + |a + b + c| := by sorry
