-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_gChar_three_sub_two
-- name    : NetFeePlatform.Competition.gChar_three_sub_two
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:49.579984+00:00
-- url     : https://prove2.me/theorems/9733ba24-0108-46f2-a840-1eee0873bddc
-- title:
--   Proof of Proposition 4, p. 50 — g(n; 3) − g(n; 2) = −ln 2 + 1/(1 − n/2) − 1/(1 − n) + γn
-- statement:
--   For every $\gamma\in\mathbb R$ and every $0<n<1$, the characterization functions for triopoly and duopoly differ by
--   $$g(n;3)-g(n;2)=-\ln2+\frac{1}{1-n/2}-\frac{1}{1-n}+\gamma n.$$
--
--   At a zero of $g(\cdot;2)$, i.e. a duopoly equilibrium whose smaller platform has share $n$, the sign of this difference is the sign of $g(n;3)$, which decides whether triopoly has an equilibrium with an even larger dominant platform.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), pp. 49–50, Appendix E.2, proof of Proposition 4

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting
import Definitions.Def_NetFeePlatform_Competition_GChar

namespace NetFeePlatform.Competition
theorem gChar_three_sub_two (γ n : ℝ) (hn0 : 0 < n) (hn1 : n < 1) :
    gChar γ 3 n - gChar γ 2 n = -Real.log 2 + 1 / (1 - n / 2) - 1 / (1 - n) + γ * n := by sorry
end NetFeePlatform.Competition
