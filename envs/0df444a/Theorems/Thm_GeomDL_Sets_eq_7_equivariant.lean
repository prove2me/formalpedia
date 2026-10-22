-- Prove2me | Theorems.Thm_GeomDL_Sets_eq_7_equivariant
-- name    : GeomDL.Sets.eq_7_equivariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:12.735454+00:00
-- url     : https://prove2.me/theorems/c0f03740-3e6c-450b-aa9a-be495e85fd78
-- title:
--   §4.1, eq. (7), p. 33 — the shared node-wise linear map F_Θ(X) = XΘ is permutation equivariant
-- statement:
--   Let $\boldsymbol\Theta\in\mathbb R^{d\times d'}$ and define $\mathbf F_{\boldsymbol\Theta}:\mathbb R^{n\times d}\to\mathbb R^{n\times d'}$ by
--
--   $$\mathbf F_{\boldsymbol\Theta}(\mathbf X)=\mathbf X\boldsymbol\Theta .$$
--
--   Then
--
--   1. $\mathbf F_{\boldsymbol\Theta}$ is permutation equivariant: $\mathbf F_{\boldsymbol\Theta}(\mathbf P\mathbf X)=\mathbf P\,\mathbf F_{\boldsymbol\Theta}(\mathbf X)$ for every permutation matrix $\mathbf P$;
--   2. the $u$-th row of $\mathbf F_{\boldsymbol\Theta}(\mathbf X)$ is the latent feature $\mathbf h_u=\boldsymbol\Theta^\top\mathbf x_u$.
--
--   This is the simplest permutation-equivariant layer: the same linear map applied to every node.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.1, eq. (7), p. 33

import Mathlib
import Definitions.Def_GeomDL_Sets_Defs

namespace GeomDL.Sets

/-- §4.1, eq. (7), p. 33: the shared node-wise linear transform `F_Θ(X) = XΘ`,
`Θ ∈ ℝ^{d×d'}`, is permutation equivariant, `F_Θ(PX) = P F_Θ(X)`, and its rows are the
latent features `h_u = Θᵀ x_u`. -/
theorem eq_7_equivariant {n d d' : ℕ} (Θ : Matrix (Fin d) (Fin d') ℝ) :
    IsPermEquivariant (nodeLinear Θ : Matrix (Fin n) (Fin d) ℝ → Matrix (Fin n) (Fin d') ℝ) ∧
      ∀ (X : Matrix (Fin n) (Fin d) ℝ) (u : Fin n), nodeLinear Θ X u = (Matrix.transpose Θ).mulVec (X u) := by sorry

end GeomDL.Sets
