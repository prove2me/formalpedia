-- Prove2me | Theorems.Thm_GeomDL_Grids_shift_equivariance
-- name    : GeomDL.Grids.shift_equivariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:24.039246+00:00
-- url     : https://prove2.me/theorems/c90a6f3a-5f9c-46ef-8080-4f1d786074e8
-- title:
--   §4.2, p. 37 — shift equivariance of convolution, SC(θ)x = C(θ)Sx
-- statement:
--   Let $n \ge 1$ and let $R$ be a commutative ring. For every filter $\theta = (\theta_0, \dots, \theta_{n-1})$ and every signal $x$ on $\mathbb Z_n$, the convolution operator $C(\theta)$ commutes with the right shift $S$:
--   $$S\,C(\theta)\,x = C(\theta)\,S\,x .$$
--
--   This is the translation (shift) equivariance of convolution: shifting the input and then convolving gives the same result as convolving and then shifting. It is the easy half of the characterisation of circulant matrices as the matrices commuting with $S$.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, p. 37, display "SC(θ)x = C(θ)Sx"

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, p. 37: shift equivariance of the convolution operator,
`SC(θ)x = C(θ)Sx` for every filter `θ` and every signal `x`. -/
theorem shift_equivariance {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (θ x : ZMod n → R) :
    shift R n *ᵥ (circulant θ *ᵥ x) = circulant θ *ᵥ (shift R n *ᵥ x) := by sorry
end GeomDL.Grids
