-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_latDet_eq_hgt_mul
-- name    : LenstraIP.Hyperplanes.latDet_eq_hgt_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:19.833984+00:00
-- url     : https://prove2.me/theorems/5af971ff-f60e-4076-8350-4af2f44ecf86
-- title:
--   §1, p. 540, (11) — d(L) = h · d(L′)
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$ ($n \ge 1$) and $L = \sum_{i=1}^n \mathbb Z b_i$. Let $L' = \sum_{i=1}^{n-1} \mathbb Z b_i$, a lattice in the hyperplane $H = \sum_{i=1}^{n-1}\mathbb R b_i$, and let $h$ be the distance of $b_n$ to $H$. Then
--   $$d(L) = h \cdot d(L'),$$
--   where $d(L) = |\det(b_1, \dots, b_n)|$ and $d(L')$ is the $(n-1)$-dimensional volume of the fundamental parallelepiped $\sum_{i=1}^{n-1}[0,1)\,b_i$ of $L'$.
--
--   This is equation (11) of §1 ("base times height"). Combined with the reducedness (7) and Hadamard's inequality (6) for $L'$, it yields the lower bound on $h$ in (12).
--
--   **Formalization Note** The paper states (11) right after assuming the basis is reduced in the sense of (7); the identity does not use (7), and the Lean statement omits it. The paper gives no formula for $d(L')$; the Lean uses the published `KannanLattice.Core.latticeDet` applied to $b_1, \dots, b_{n-1}$, which is the product $\prod_{i<n} |b_i^*|$ of the Gram–Schmidt lengths, i.e. the $(n-1)$-volume of the fundamental parallelepiped. $d(L)$ is the absolute determinant of the column matrix, as on p. 540, and $h$ is the metric distance from $b_n$ to $H$, not a Gram–Schmidt length. $n = k+1$, $b_n$ is `b (Fin.last k)`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, p. 540, (11)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, p. 540, (11): `d(L) = h · d(L′)`, where `L′ = Σ_{i<n} ℤ bᵢ`, `h` is the
distance of `bₙ` to `H = Σ_{i<n} ℝ bᵢ`, and `d(L′)` is the `(n−1)`-volume of the fundamental
parallelepiped of `b₁, …, bₙ₋₁` (the product of their Gram–Schmidt lengths). -/
theorem latDet_eq_hgt_mul (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) :
    latDet b = hgt b * latticeDet (b ∘ Fin.castSucc) := by sorry

end LenstraIP.Hyperplanes
