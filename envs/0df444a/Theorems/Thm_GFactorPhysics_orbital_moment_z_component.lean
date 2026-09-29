-- Prove2me | Theorems.Thm_GFactorPhysics_orbital_moment_z_component
-- name    : GFactorPhysics.orbital_moment_z_component
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:46:56.237017+00:00
-- url     : https://prove2.me/theorems/3871be20-64ab-411e-baf6-2a0884ded62a
-- title:
--   $z$ component of the electron orbital moment: $\mu_z = -g_L\mu_B m_\ell$
-- statement:
--   Let $g_L,\mu_B,\hbar,m_\ell$ be real numbers with $\hbar\ne0$, and let $\mathbf L\in\mathbb R^3$ be an orbital angular momentum whose $z$ component is $L_z=m_\ell\hbar$. For the electron orbital moment $\boldsymbol\mu_L=-g_L\frac{\mu_B}{\hbar}\mathbf L$,
--
--   $$\mu_z = -g_L\,\mu_B\,m_\ell,$$
--
--   and in particular, when $g_L=1$, $\mu_z=-\mu_B m_\ell$.
--
--   **Formalization Note** The $z$ component is component index $2$ of a vector in `Fin 3 → ℝ`.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); section "Electron orbital g-factor": definition $\mu_L = -g_L\frac{\mu_B}{\hbar}\mathbf L$, formula $\mu_z = -g_L\mu_B m_\ell$ and "since $g_L = 1$, the result is $-\mu_B m_\ell$".

import Definitions.Def_GFactorPhysics_Defs
import Mathlib

namespace GFactorPhysics
theorem orbital_moment_z_component (g_L μB hbar m_l : ℝ) (L : Fin 3 → ℝ)
    (hhbar : hbar ≠ 0) (hLz : L 2 = m_l * hbar) :
    electronOrbitalMagneticMoment g_L μB hbar L 2 = -g_L * μB * m_l ∧
      (g_L = 1 → electronOrbitalMagneticMoment g_L μB hbar L 2 = -μB * m_l) := by sorry
end GFactorPhysics
