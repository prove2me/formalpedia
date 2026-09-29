-- Prove2me | Theorems.Thm_LipariNeutrino_sin_add_sin_sub_sin_add
-- name    : LipariNeutrino.sin_add_sin_sub_sin_add
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T11:47:25.175528+00:00
-- url     : https://prove2.me/theorems/4d72fd97-f7d8-4d0e-a6f7-bda8ba21db00
-- title:
--   $\sin a+\sin b-\sin(a+b)=4\sin\frac a2\sin\frac b2\sin\frac{a+b}2$
-- statement:
--   For all real numbers $a,b$,
--
--   $$\sin a+\sin b-\sin(a+b)=4\,\sin\frac a2\,\sin\frac b2\,\sin\frac{a+b}2.$$
--
--   This identity turns the three CP-odd sine terms of the three-flavour oscillation probability into a single product of three sines.
-- source:
--   P. Lipari, *Introduction to Neutrino Physics* (lecture notes, uploaded PDF), Section 4, §4.3, p. 136, Eq. (72).

import Mathlib

namespace LipariNeutrino

theorem sin_add_sin_sub_sin_add (a b : ℝ) :
    Real.sin a + Real.sin b - Real.sin (a + b) =
      4 * Real.sin (a / 2) * Real.sin (b / 2) * Real.sin ((a + b) / 2) := by sorry

end LipariNeutrino
