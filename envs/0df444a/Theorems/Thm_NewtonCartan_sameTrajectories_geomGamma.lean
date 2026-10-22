-- Prove2me | Theorems.Thm_NewtonCartan_sameTrajectories_geomGamma
-- name    : NewtonCartan.sameTrajectories_geomGamma
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:13:57.661993+00:00
-- url     : https://prove2.me/theorems/7cc654f8-a85b-48dd-8922-34260196cd94
-- title:
--   Geometrization preserves Newtonian trajectories
-- statement:
--   Let $\nabla$ be any torsion-free derivative operator on $\mathbb R^4$ and $\varphi$ any smooth scalar field. Writing $\widetilde{\nabla}$ for the Trautman geometrization $(\nabla,-t_b t_c\nabla^a\varphi)$, a unit-timelike curve is a $\widetilde{\nabla}$-geodesic if and only if it satisfies Newton's law $\xi^n\nabla_n\xi^a=-\nabla^a\varphi$. Equivalently, $\mathrm{SameTrajectories}(\nabla,\varphi,\widetilde{\nabla})$ holds.
--
--   This is the empirical-content half of Weatherall's Prop. 2.1 / Malament Prop. 4.2.1 (G1), and is reused in the Trautman recovery (Prop. 2.2).
-- source:
--   J. O. Weatherall, arXiv:1411.5757, Prop. 2.1; D. B. Malament, Topics in the Foundations of GR and NGT (2012), Prop. 4.2.1 (G1)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

theorem sameTrajectories_geomGamma (Γ : Conn) (φ : E → ℝ) :
    SameTrajectories Γ φ (geomΓ Γ φ) := by sorry

end NewtonCartan
