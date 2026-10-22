-- Prove2me | Theorems.Thm_NewtonCartan_exists_potential_of_tt_riem
-- name    : NewtonCartan.exists_potential_of_tt_riem
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:15:52.147209+00:00
-- url     : https://prove2.me/theorems/f220ec52-9624-430a-a874-279f2a82ca77
-- title:
--   Poincaré recovery of $\varphi$ from the Trautman curvature form
-- statement:
--   Assume a classical connection $\widetilde{\nabla}$ satisfies CurvConds for a smooth density $\rho$, and that its Riemann tensor has already been reduced to the Trautman form
--   $$
--   R^a{}_{bcd}=t_b(t_c F^a{}_d-t_d F^a{}_c),\qquad F^a{}_d=R^a{}_{00d}.
--   $$
--   Then there exists a smooth potential $\varphi$ such that the gauge-transformed connection
--   $$\nabla=(\widetilde{\nabla},\,t_b t_c\nabla^a\varphi)$$
--   is flat and compatible and satisfies Poisson's equation $\nabla^a\nabla_a\varphi=4\pi\rho$.
--
--   This packages the Poincaré-lemma integrability of $F^a{}_d$ (from CurvConds (2)) together with the verification that the resulting gauge is an object of NG obeying Poisson (from CurvConds (1)).
-- source:
--   D. B. Malament, Topics in the Foundations of GR and NGT (2012), Prop. 4.2.5; Weatherall arXiv:1411.5757 Prop. 2.2

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- Poincaré / integrability step of Trautman recovery: if the Riemann tensor of a classical
`Γt` has the Trautman $t_b$-form coming from CurvConds, then there is a smooth potential `φ`
whose covectorially differentiated raised gradient reproduces `R^a{}_{00d}`, and for which
the gauge `gaugeΓ Γt φ` is an NG object obeying Poisson. -/
theorem exists_potential_of_tt_riem (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hρ : ContDiff ℝ ∞ ρ) (hcurv : CurvConds Γt ρ)
    (hform : ∀ x a b c d,
      riem Γt x a b c d =
        tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c)) :
    ∃ φ : E → ℝ, IsNG (gaugeΓ Γt φ) φ ∧ Poisson (gaugeΓ Γt φ) φ ρ := by sorry

end NewtonCartan
