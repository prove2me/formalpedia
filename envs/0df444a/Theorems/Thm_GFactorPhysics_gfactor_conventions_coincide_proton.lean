-- Prove2me | Theorems.Thm_GFactorPhysics_gfactor_conventions_coincide_proton
-- name    : GFactorPhysics.gfactor_conventions_coincide_proton
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:44:51.070585+00:00
-- url     : https://prove2.me/theorems/459ee45d-ae93-4849-9a42-663b9b96d44b
-- title:
--   The Dirac and nuclear-magneton definitions of $g$ coincide for the proton
-- statement:
--   Let $e>0$, $\hbar>0$ and $m_p>0$, and let $\mathbf S\in\mathbb R^3$ be a nonzero spin vector. Suppose a particle of mass $m_p$ has magnetic moment $\boldsymbol\mu$ that is described both by the Dirac-particle formula with g-factor $g_1$ and by the nuclear-magneton formula with g-factor $g_2$:
--
--   $$g_1\,\frac{e}{2m_p}\,\mathbf S \;=\; \boldsymbol\mu \;=\; g_2\,\frac{\mu_N}{\hbar}\,\mathbf S,\qquad \mu_N=\frac{e\hbar}{2m_p}.$$
--
--   Then $g_1=g_2$.
--
--   This makes precise the article's remark that the two definitions of the g-factor coincide for the proton, the particle whose mass enters the nuclear magneton.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); opening paragraph ("In nuclear physics, the nuclear magneton replaces the classically expected magnetic moment ... The two definitions coincide for the proton.") together with sections "Dirac particle" and "Baryon or nucleus".

import Definitions.Def_GFactorPhysics_Defs
import Mathlib

namespace GFactorPhysics
theorem gfactor_conventions_coincide_proton (g₁ g₂ e hbar m_p : ℝ) (S : Fin 3 → ℝ)
    (he : 0 < e) (hhbar : 0 < hbar) (hm_p : 0 < m_p) (hS : S ≠ 0)
    (h : diracMagneticMoment g₁ e m_p S =
      nuclearMagneticMoment g₂ (nuclearMagneton e hbar m_p) hbar S) :
    g₁ = g₂ := by sorry
end GFactorPhysics
