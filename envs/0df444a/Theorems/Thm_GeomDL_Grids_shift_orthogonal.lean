-- Prove2me | Theorems.Thm_GeomDL_Grids_shift_orthogonal
-- name    : GeomDL.Grids.shift_orthogonal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:15.527755+00:00
-- url     : https://prove2.me/theorems/b0b9513f-a6cc-42cc-aa0e-37250c6b8cdf
-- title:
--   §4.2, side-note p. 37 — the left shift is Sᵀ, and S is orthogonal: SᵀS = SSᵀ = I
-- statement:
--   Let $n \ge 1$, let $R$ be a commutative ring and let $S$ be the right shift on $\mathbb Z_n$. Its transpose is the left shift,
--   $$(S^\top x)_u = x_{u+1 \bmod n} \qquad \text{for every } x \text{ and } u,$$
--   and shifting left and then right (or vice versa) is the identity:
--   $$S^\top S = S S^\top = I .$$
--
--   Thus $S$ is an orthogonal (permutation) matrix; this is the fact behind the orthogonality of its eigenvectors used in the derivation of the Fourier transform.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, side-note p. 37, "The left shift operator is given by S⊤ … S is orthogonal: S⊤S = SS⊤ = I"

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, side-note p. 37: the left shift operator is `Sᵀ`, i.e.
`(Sᵀx)_u = x_{u+1}`, and `S` is orthogonal: `SᵀS = SSᵀ = I`. -/
theorem shift_orthogonal {R : Type*} [CommRing R] {n : ℕ} [NeZero n] :
    (∀ (x : ZMod n → R) (u : ZMod n), ((shift R n)ᵀ *ᵥ x) u = x (u + 1)) ∧
      (shift R n)ᵀ * shift R n = 1 ∧ shift R n * (shift R n)ᵀ = 1 := by sorry
end GeomDL.Grids
