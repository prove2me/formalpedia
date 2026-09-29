-- Prove2me | Theorems.Thm_GFactorPhysics_nuclearMagneticMoment_eq
-- name    : GFactorPhysics.nuclearMagneticMoment_eq
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:41:17.781243+00:00
-- url     : https://prove2.me/theorems/5f89c069-2cb5-4b7e-8234-99bd64af91dc
-- title:
--   Nuclear-magneton form of the moment: $g\frac{\mu_N}{\hbar}\mathbf I = g\frac{e}{2m_p}\mathbf I$
-- statement:
--   Let $g,e,\hbar,m_p$ be real numbers with $\hbar\neq0$, let $\mathbf I\in\mathbb R^3$, and let $\mu_N=\frac{e\hbar}{2m_p}$ be the nuclear magneton. Then
--
--   $$g\,\frac{\mu_N}{\hbar}\,\mathbf I \;=\; g\,\frac{e}{2m_p}\,\mathbf I .$$
--
--   This is the second equality in the article's defining formula for the g-factor of a nucleon or nucleus.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); section "Baryon or nucleus", displayed formula $\mu = g\frac{\mu_N}{\hbar}\mathbf I = g\frac{e}{2m_p}\mathbf I$.

import Definitions.Def_GFactorPhysics_Defs
import Mathlib

namespace GFactorPhysics
theorem nuclearMagneticMoment_eq (g e hbar m_p : ℝ) (I : Fin 3 → ℝ) (hhbar : hbar ≠ 0) :
    nuclearMagneticMoment g (nuclearMagneton e hbar m_p) hbar I = (g * e / (2 * m_p)) • I := by sorry
end GFactorPhysics
