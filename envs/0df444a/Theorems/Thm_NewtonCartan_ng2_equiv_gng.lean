-- Prove2me | Theorems.Thm_NewtonCartan_ng2_equiv_gng
-- name    : NewtonCartan.ng2_equiv_gng
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-20T23:18:09.811463+00:00
-- url     : https://prove2.me/theorems/039af4ee-ec65-4753-956e-e96eb596db6a
-- title:
--   Prop. 6.1: NG2 is equivalent to GNG
-- statement:
--   Spacetime is $\mathbb R^4$ in a global chart (index 0 = time) with $t_a=dx^0$, $h^{ab}=\mathrm{diag}(0,1,1,1)$; a derivative operator is a smooth symmetric Christoffel field $\Gamma^a{}_{bc}$; curvature in Malament's convention $\xi^bR^a{}_{bcd}=-2\nabla_{[c}\nabla_{d]}\xi^a$, $R_{bc}=R^n{}_{bcn}$; $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$ is the geometrization; timelike curves have unit tangent $t_a\xi^a=1$. Geometrization $(\nabla,\varphi)\mapsto\tilde\nabla$, $(f,\psi)\mapsto f$ maps NG$_2$ objects to GNG objects with the same allowed trajectories and NG$_2$ arrows to GNG arrows; every GNG arrow between geometrizations is the image of a unique NG$_2$ arrow (full and faithful); and every GNG object is GNG-isomorphic to a geometrization (essentially surjective). Hence NG$_2\simeq$ GNG preserving empirical content.
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Prop. 6.1 (p. 18) and its proof in Appendix A (pp. 23-24)

import Definitions.Def_NewtonCartan_defs

open scoped ContDiff

namespace NewtonCartan

/-- **Prop. 6.1 (Weatherall).** Geometrization is an equivalence of categories `NG₂ ≃ GNG` that preserves
empirical content: it sends objects of NG₂ to objects of GNG with the same allowed trajectories,
sends arrows `(f, ψ)` to `f`, is full and faithful (every GNG arrow between geometrizations lifts to
a unique NG₂ arrow), and is essentially surjective. -/
theorem ng2_equiv_gng :
    (∀ Γ φ, IsNG Γ φ → IsGNG (geomΓ Γ φ) ∧ SameTrajectories Γ φ (geomΓ Γ φ)) ∧
    (∀ Γ φ Γ' φ' f ψ, IsNG Γ φ → IsNG Γ' φ' → IsNG2Arrow Γ φ Γ' φ' f ψ →
      IsGNGArrow (geomΓ Γ φ) (geomΓ Γ' φ') f) ∧
    (∀ Γ φ Γ' φ' f, IsNG Γ φ → IsNG Γ' φ' → IsGNGArrow (geomΓ Γ φ) (geomΓ Γ' φ') f →
      ∃! ψ : E → ℝ, IsNG2Arrow Γ φ Γ' φ' f ψ) ∧
    (∀ Γt, IsGNG Γt → ∃ (Γ : Conn) (φ : E → ℝ) (f : E ≃ E), IsNG Γ φ ∧
      IsGNGArrow (geomΓ Γ φ) Γt f ∧ IsGNGArrow Γt (geomΓ Γ φ) f.symm) := by sorry

end NewtonCartan
