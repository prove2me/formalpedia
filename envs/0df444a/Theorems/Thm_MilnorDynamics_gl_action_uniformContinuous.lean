-- Prove2me | Theorems.Thm_MilnorDynamics_gl_action_uniformContinuous
-- name    : MilnorDynamics.gl_action_uniformContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T03:12:26.254946+00:00
-- url     : https://prove2.me/theorems/4d0c4cda-c00f-4885-9182-a5bdabace744
-- title:
--   Mobius maps are uniformly continuous for the chordal metric, in both directions
-- statement:
--   **Mobius maps are uniformly continuous for the spherical metric.** Fix an invertible complex $2\times 2$ matrix $g$, acting on the Riemann sphere $\hat{\mathbb C}$ by fractional linear transformation. Then both the map $x\mapsto g\cdot x$ and its inverse $x\mapsto g^{-1}\cdot x$ are uniformly continuous with respect to the chordal distance $\chi$:
--   $$\forall \varepsilon>0,\ \exists\delta>0,\ \forall x,y,\quad \chi(x,y)<\delta \implies \chi(g\cdot x,g\cdot y)<\varepsilon .$$
--
--   This is the quantitative continuity input for the Mobius normalisation step in Milnor's proof of Theorem 3.7. Because normality of a family of sphere-valued maps is defined by local uniform convergence in the chordal metric, knowing that a Mobius transformation and its inverse are uniformly continuous lets a locally uniformly convergent sequence be pushed through the transformation in either direction. On the compact sphere this is the usual compactness fact that a homeomorphism is uniformly continuous; stated here directly in terms of the explicit chordal distance of the project's definition module.
--
--   **Formalization Note** The Mobius action is `OnePoint.instGLAction`, and `chordalDist` is the explicit stereographic distance from `Definitions.Def_MilnorDynamics_NormalFamilies`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3; continuity of Mobius transformations with respect to the spherical metric.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem gl_action_uniformContinuous (g : GL (Fin 2) ℂ) :
    (∀ ε > 0, ∃ δ > 0, ∀ x y : OnePoint ℂ,
        chordalDist x y < δ → chordalDist (g • x) (g • y) < ε) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ x y : OnePoint ℂ,
        chordalDist x y < δ → chordalDist (g⁻¹ • x) (g⁻¹ • y) < ε) := by sorry

end MilnorDynamics
