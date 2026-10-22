-- Prove2me | Theorems.Thm_GeomDL_Grids_circulant_mulVec_eq_conv
-- name    : GeomDL.Grids.circulant_mulVec_eq_conv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:10.989728+00:00
-- url     : https://prove2.me/theorems/4a269ece-2baa-4348-9b4b-933d4915af0e
-- title:
--   §4.2, p. 37 — C(θ)x = x ⋆ θ, and the shift S = C(0, 1, 0, …, 0) moves vectors right: (Sx)_u = x_{u−1}
-- statement:
--   Let $n \ge 1$, let $R$ be a commutative ring, and index vectors by $\mathbb Z_n$. Circulant matrices are convolutions: for every filter $\theta$ and every signal $x$,
--   $$C(\theta)\,x = x \star \theta .$$
--   Moreover the circulant matrix $S = C(0, 1, 0, \dots, 0)$ shifts vectors to the right by one position:
--   $$(Sx)_u = x_{u-1 \bmod n} \qquad \text{for all } u \in \mathbb Z_n .$$
--
--   The first identity justifies calling circulant matrices convolution operators; the second fixes the direction of the shift used throughout the section.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, p. 37, "as one has C(θ)x = x ⋆ θ" and "shifts vectors to the right by one position" (convolution display on p. 36)

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, p. 37: `C(θ)x = x ⋆ θ`, and the circulant matrix `S` of
`θ = (0, 1, 0, …, 0)ᵀ` shifts vectors to the right by one position: `(Sx)_u = x_{u-1}`. -/
theorem circulant_mulVec_eq_conv {R : Type*} [CommRing R] {n : ℕ} [NeZero n] :
    (∀ θ x : ZMod n → R, circulant θ *ᵥ x = conv x θ) ∧
      ∀ (x : ZMod n → R) (u : ZMod n), (shift R n *ᵥ x) u = x (u - 1) := by sorry
end GeomDL.Grids
