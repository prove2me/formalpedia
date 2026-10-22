-- Prove2me | Theorems.Thm_NewtonCartan_ng1_not_equiv_gng
-- name    : NewtonCartan.ng1_not_equiv_gng
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-20T23:17:52.87493+00:00
-- url     : https://prove2.me/theorems/e0034ffc-ef60-41e4-94f9-53f3cb869808
-- title:
--   Table 1: NG1 is not equivalent to GNG
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. There is no map $F$ from NG objects (flat compatible $\nabla$ with smooth $\varphi$) to GNG objects such that each $F(\nabla,\varphi)$ has the Newtonian trajectories of $(\nabla,\varphi)$ as its timelike geodesics and, for all objects $A,B$, the NG$_1$ arrows $A\to B$ (diffeomorphisms preserving $t,h,\nabla,\varphi$) are in bijection with the GNG arrows $F(A)\to F(B)$.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Section 6, p. 18 and Table 1 (stated in prose, without proof)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **NG₁ is not equivalent to GNG (Weatherall §6, p. 18).** There is no map from objects of NG₁ to
objects of GNG that preserves empirical content and induces bijections on hom-sets; in particular
there is no equivalence of categories `NG₁ ≃ GNG` preserving empirical content. -/
theorem ng1_not_equiv_gng :
    ¬ ∃ F : {p : Conn × (E → ℝ) // IsNG p.1 p.2} → {Γ : Conn // IsGNG Γ},
      (∀ A, SameTrajectories A.1.1 A.1.2 (F A).1) ∧
      ∀ A B, Nonempty ({f : E ≃ E // IsNG1Arrow A.1.1 A.1.2 B.1.1 B.1.2 f} ≃
        {f : E ≃ E // IsGNGArrow (F A).1 (F B).1 f}) := by sorry

end NewtonCartan
