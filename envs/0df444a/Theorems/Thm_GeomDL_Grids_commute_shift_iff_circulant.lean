-- Prove2me | Theorems.Thm_GeomDL_Grids_commute_shift_iff_circulant
-- name    : GeomDL.Grids.commute_shift_iff_circulant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:41:18.267083+00:00
-- url     : https://prove2.me/theorems/75eee33d-9837-4ae4-a246-3ac0a448e96d
-- title:
--   §4.2, p. 37 — an n × n matrix commutes with the cyclic shift S if and only if it is circulant
-- statement:
--   Let $n \ge 1$, let $R$ be a commutative ring, and let $S$ be the right shift on $\mathbb Z_n$, i.e. the circulant matrix of $(0, 1, 0, \dots, 0)$. For every $n \times n$ matrix $M$ with entries in $R$, indexed by $\mathbb Z_n$,
--   $$M S = S M \iff M = C(\theta) \text{ for some } \theta = (\theta_0, \dots, \theta_{n-1}) \in R^n ,$$
--   where $C(\theta) = (\theta_{u - v \bmod n})_{u,v}$ is the circulant matrix of $\theta$.
--
--   The direction "$\Leftarrow$" is the commutativity of circulant matrices, which gives the shift equivariance of convolution. The direction "$\Rightarrow$" says that the linear shift-equivariant maps are exactly the convolutions, which lets one define convolution as a translation-equivariant linear operation.
--
--   **Formalization Note** The page states this claim tentatively ("the opposite direction appears to be true as well"); it is a true theorem and is stated here without hedging. It holds over any commutative ring and for every $n \ge 1$ (for $n = 1$ both sides hold for every matrix).
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, p. 37, "a matrix is circulant iff it commutes with shift"

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open Matrix

namespace GeomDL.Grids
/-- Bronstein et al. §4.2, p. 37: "a matrix is circulant iff it commutes with shift".
An `n × n` matrix `M` over a commutative ring commutes with the right shift `S` if and only
if `M = C(θ)` for some vector `θ`. -/
theorem commute_shift_iff_circulant {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (M : Matrix (ZMod n) (ZMod n) R) :
    M * shift R n = shift R n * M ↔ ∃ θ : ZMod n → R, M = circulant θ := by sorry
end GeomDL.Grids
