-- Prove2me | Theorems.Thm_NewtonCartan_riem_tt_form_of_curvConds
-- name    : NewtonCartan.riem_tt_form_of_curvConds
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:15:56.417909+00:00
-- url     : https://prove2.me/theorems/6325d328-1f04-4d9a-9d5a-02f106d3a357
-- title:
--   CurvConds force the Trautman $t_b$-factor form of Riemann
-- statement:
--   Let $(\mathbb R^4,t_a,h^{ab},\widetilde{\nabla})$ be a classical spacetime satisfying the Trautman curvature condition $R^{ab}{}_{cd}=0$. Then the Riemann tensor vanishes on spatial middle indices, and therefore admits the factored form
--   $$
--   R^a{}_{bcd}=t_b\bigl(t_c F^a{}_d-t_d F^a{}_c\bigr),
--   $$
--   where $F^a{}_d:=R^a{}_{00d}$.
--
--   This is the first structural step of Malament's Trautman recovery (Prop. 4.2.5): it isolates the gravitational field strength $F^a{}_d$ from the curvature of $\widetilde{\nabla}$.
-- source:
--   D. B. Malament, Topics in the Foundations of GR and NGT (2012), Prop. 4.2.5 and discussion of (4.2.18)–(4.2.20); Weatherall arXiv:1411.5757 Prop. 2.2

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- From CurvConds (3) (and classical structure), the Riemann tensor of `Γt` vanishes whenever
the middle index is spatial, and hence
`R^a{}_{bcd} = t_b (t_c F^a{}_d - t_d F^a{}_c)` with `F^a{}_d = R^a{}_{00d}`. -/
theorem riem_tt_form_of_curvConds (Γt : Conn) (ρ : E → ℝ)
    (hΓt : IsClassical Γt) (hcurv : CurvConds Γt ρ) (x : E) (a b c d : Fin 4) :
    riem Γt x a b c d =
      tt b * (tt c * riem Γt x a 0 0 d - tt d * riem Γt x a 0 0 c) := by sorry

end NewtonCartan
