-- Prove2me | Theorems.Thm_NewtonCartan_exists_recovery_potential
-- name    : NewtonCartan.exists_recovery_potential
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:13:46.275805+00:00
-- url     : https://prove2.me/theorems/3c870a5f-b3d7-43f9-a47c-f69040fd2d70
-- title:
--   Existence of a recovering potential for CurvConds
-- statement:
--   Let $(\mathbb R^4,t_a,h^{ab},\widetilde{\nabla})$ be a classical spacetime satisfying the Trautman–Malament curvature conditions (1)–(3) for a smooth mass density $\rho$. Then there exists a smooth gravitational potential $\varphi$ such that the gauge-transformed connection
--   $$\nabla=(\widetilde{\nabla},\,t_b t_c\widetilde{\nabla}^a\varphi)$$
--   (i.e. $\Gamma^a{}_{bc}=\widetilde{\Gamma}^a{}_{bc}-t_b t_c\nabla^a\varphi$) is flat and compatible, and $(\nabla,\varphi)$ satisfies Poisson's equation $\nabla^a\nabla_a\varphi=4\pi\rho$.
--
--   In the formalization, $\nabla$ is written `gaugeΓ Γt φ`. This is the existence/Poincaré-lemma content of Weatherall Prop. 2.2 / Malament Prop. 4.2.5; together with the identity $\mathrm{geom}\Gamma(\mathrm{gauge}\Gamma(\widetilde{\Gamma},\varphi),\varphi)=\widetilde{\Gamma}$ it yields Trautman recovery.
-- source:
--   J. O. Weatherall, arXiv:1411.5757, Prop. 2.2 (pp. 4-5); D. B. Malament, Topics in the Foundations of GR and NGT (2012), Prop. 4.2.5

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

theorem exists_recovery_potential (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ) :
    ∃ φ : E → ℝ, IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by sorry

end NewtonCartan
