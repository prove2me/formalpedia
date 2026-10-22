-- Prove2me | Theorems.Thm_NewtonCartan_geom_naturality
-- name    : NewtonCartan.geom_naturality
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-20T23:17:37.146961+00:00
-- url     : https://prove2.me/theorems/d3ab322d-c0e1-4198-9ea5-9015ec47d4a7
-- title:
--   App. A: geometrization commutes with diffeomorphisms
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. Let $f$ be a diffeomorphism of $\mathbb R^4$ preserving $t_a$ and $h^{ab}$, and $\varphi,\varphi'$ smooth with $\varphi'\circ f=\varphi$. Then $f$ carries $\nabla$ to $\nabla'$ iff it carries $(\nabla,-t_bt_c\nabla^a\varphi)$ to $(\nabla',-t_bt_c\nabla'^a\varphi')$.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Appendix A, proof of Prop. 6.1 (pp. 23-24)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **Naturality of geometrization (Weatherall, App. A, proof of Prop. 6.1).** A diffeomorphism
preserving the classical metrics and carrying `φ` to `φ'` carries `∇` to `∇'` iff it carries the
geometrized operator `(∇, -t_b t_c ∇^a φ)` to `(∇', -t_b t_c ∇'^a φ')`. -/
theorem geom_naturality (Γ Γ' : Conn) (φ φ' : E → ℝ) (f : E ≃ E) (hf : IsDiffeo f)
    (hm : PreservesMetrics f) (hφ : ContDiff ℝ ∞ φ) (hφ' : ContDiff ℝ ∞ φ')
    (hpush : ∀ x, φ' (f x) = φ x) :
    MapsConn f Γ Γ' ↔ MapsConn f (geomΓ Γ φ) (geomΓ Γ' φ') := by sorry

end NewtonCartan
