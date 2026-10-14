-- Prove2me | Theorems.Thm_Multihoming_Hump_r1_r2_pos
-- name    : Multihoming.Hump.r1_r2_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:33.316187+00:00
-- url     : https://prove2.me/theorems/eddaed9a-27db-4a4d-8f6e-37f6e73d4853
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — r₁ > 0 and r₂ > 0 when 2t − e > 0
-- statement:
--   Let $t>0$ and $0\le e<2t$. Then the roots of Appendix A1,
--   $$r_1=\frac{t\sqrt{3(4t^2-e^2)}-2t^2+et}{2(e+t)},\qquad r_2=\frac{t\left(2t-e+\sqrt{3(4t^2-e^2)}\right)}{2(e+t)},$$
--   are both positive: $r_1>0$ and $r_2>0$.
--
--   Together with the factorization of $d\pi^M/d\mu$ this gives the sign of the profit's derivative near $\mu=0$.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, sentence after the definitions of r₁, r₂

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: r₁ and r₂ are positive when 2t − e > 0. -/
theorem r1_r2_pos (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    0 < r1 t e ∧ 0 < r2 t e := by sorry

end Multihoming.Hump
