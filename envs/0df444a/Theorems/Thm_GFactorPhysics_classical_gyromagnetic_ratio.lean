-- Prove2me | Theorems.Thm_GFactorPhysics_classical_gyromagnetic_ratio
-- name    : GFactorPhysics.classical_gyromagnetic_ratio
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T20:50:31.381826+00:00
-- url     : https://prove2.me/theorems/6098d153-7a31-43de-9ade-e2a4981df819
-- title:
--   Classical point charges with uniform charge-to-mass ratio have $g = 1$
-- statement:
--   Consider $n$ classical point particles with masses $m_i>0$, charges $q_i$, positions $\mathbf r_i\in\mathbb R^3$ and velocities $\mathbf v_i\in\mathbb R^3$, and suppose the charge-to-mass ratio is the same for all of them: there is $\kappa\in\mathbb R$ with $q_i=\kappa m_i$ for every $i$. Let $Q=\sum_i q_i$ and $M=\sum_i m_i$. Then the magnetic moment $\boldsymbol\mu=\sum_i\frac{q_i}{2}\mathbf r_i\times\mathbf v_i$ and the angular momentum $\mathbf L=\sum_i m_i\mathbf r_i\times\mathbf v_i$ satisfy
--
--   $$\boldsymbol\mu \;=\; 1\cdot\frac{Q}{2M}\,\mathbf L .$$
--
--   In the language of the article, the moment is given by the Dirac-particle formula $\boldsymbol\mu=g\frac{e}{2m}\mathbf S$ with $g=1$, charge $Q$, mass $M$ and angular momentum $\mathbf L$: the classical particle that serves as the reference in the definition of the g-factor has g-factor exactly $1$.
--
--   **Formalization Note** For $n=0$ both sides are the zero vector. The right-hand side is written with the mission's Dirac-moment definition at $g=1$.
-- source:
--   Wikipedia, "g-factor (physics)" (PDF snapshot supplied by the user, `G-factor_(physics).pdf`), https://en.wikipedia.org/wiki/G-factor_(physics); opening paragraph ("the ratio of the magnetic moment ... to that expected of a classical particle of the same charge and angular momentum") and section "Electron orbital g-factor" ("the derivation of the classical magnetogyric ratio"). The article states this baseline without deriving it.

import Definitions.Def_GFactorPhysics_Defs
import Mathlib

namespace GFactorPhysics
theorem classical_gyromagnetic_ratio {n : ℕ} (q m : Fin n → ℝ) (r v : Fin n → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (κ : ℝ) (hq : ∀ i, q i = κ * m i) :
    classicalMagneticMoment q r v =
      diracMagneticMoment 1 (∑ i, q i) (∑ i, m i) (classicalAngularMomentum m r v) := by sorry
end GFactorPhysics
