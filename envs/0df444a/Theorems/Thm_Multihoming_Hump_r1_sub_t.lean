-- Prove2me | Theorems.Thm_Multihoming_Hump_r1_sub_t
-- name    : Multihoming.Hump.r1_sub_t
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:38.33863+00:00
-- url     : https://prove2.me/theorems/1dc82737-4021-408b-91ba-5ae2c465c775
-- title:
--   Appendix A1, PDF p. 28 (printed p. 22) — r₁ − t = −t(e + 4t − √(3(4t² − e²)))/(2(e + t)), and the numerator is positive
-- statement:
--   Let $t>0$ and $0\le e<2t$, and let $r_1$ be the root of Appendix A1. Then
--   $$r_1-t=-t\,\frac{e+4t-\sqrt{3(4t^2-e^2)}}{2(e+t)},$$
--   and $e+4t-\sqrt{3(4t^2-e^2)}>0$. In particular $r_1<t$.
--
--   This locates the profit's peak $r_1$ strictly inside $[0,t)$ at its right end.
-- source:
--   Foros, Kind & Stähler, Endogenous multihoming and network effects: PlayStation, Xbox, or both?, SNF Working Paper No. 16/21 (NHH Bergen, December 2021; Management Science DOI 10.1287/mnsc.2022.00613), PDF p. 28 (printed p. 22), Appendix A1, display r₁ − t

import Mathlib
import Definitions.Def_Multihoming_Hump_Model

namespace Multihoming.Hump

/-- Appendix A1, PDF p. 28: r₁ − t = −t (e + 4t − √(3(4t² − e²)))/(2(e + t)), and
e + 4t − √(3(4t² − e²)) is positive. -/
theorem r1_sub_t (t e : ℝ) (ht : 0 < t) (he0 : 0 ≤ e) (he : e < 2 * t) :
    r1 t e - t = -t * ((e + 4 * t - Real.sqrt (3 * (4 * t ^ 2 - e ^ 2))) / (2 * (e + t))) ∧
    0 < e + 4 * t - Real.sqrt (3 * (4 * t ^ 2 - e ^ 2)) := by sorry

end Multihoming.Hump
