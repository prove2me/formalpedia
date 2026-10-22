-- Prove2me | Theorems.Thm_NewtonCartan_riem_geomGamma
-- name    : NewtonCartan.riem_geomGamma
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-21T05:40:23.194256+00:00
-- url     : https://prove2.me/theorems/75ddebbc-3e82-4f75-8d93-4907d1d39d49
-- title:
--   Malament (4.2.8): Riemann tensor after Trautman geometrization
-- statement:
--   Let $(\mathbb R^4,t_a,h^{ab},\nabla)$ be a flat classical spacetime with smooth potential $\varphi$, and let $\tilde\nabla=(\nabla,-t_bt_c\nabla^a\varphi)$ be its Trautman geometrization. Then the Riemann curvature of $\tilde\nabla$ is
--   $$\tilde R^a{}_{bcd}=t_b\bigl(t_c\nabla_d\nabla^a\varphi-t_d\nabla_c\nabla^a\varphi\bigr).$$
--   Quadratic $C\cdot C$ terms vanish because $\nabla^a\varphi$ is spatial; mixed $C\Gamma$ terms vanish by $\nabla t=0$.
-- source:
--   D. B. Malament, Topics… (2012), Prop. 4.2.1 proof, eq. (4.2.8) (p. 268); Weatherall arXiv:1411.5757 Prop. 2.1 (G3)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

theorem riem_geomGamma (Γ : Conn) (φ : E → ℝ) (hNG : IsNG Γ φ) (x : E) (a b c d : Fin 4) :
    riem (geomΓ Γ φ) x a b c d =
      tt b * (tt c * (pd (fun y => gradUp φ y a) d x +
          ∑ e : Fin 4, Γ x a d e * gradUp φ x e) -
        tt d * (pd (fun y => gradUp φ y a) c x +
          ∑ e : Fin 4, Γ x a c e * gradUp φ x e)) := by sorry

end NewtonCartan
