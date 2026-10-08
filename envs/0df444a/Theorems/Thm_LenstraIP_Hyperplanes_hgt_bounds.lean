-- Prove2me | Theorems.Thm_LenstraIP_Hyperplanes_hgt_bounds
-- name    : LenstraIP.Hyperplanes.hgt_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:34.063658+00:00
-- url     : https://prove2.me/theorems/10986148-1595-4c7d-ba35-1e084f5a62d9
-- title:
--   §1, pp. 540–541, (12) — for a reduced basis, c₂⁻¹·|bₙ| ≤ h ≤ |bₙ|
-- statement:
--   Let $b_1, \dots, b_n$ be a basis of $\mathbb R^n$ ($n \ge 1$), $L = \sum_i \mathbb Z b_i$, and let $c_2$ be a real number such that the basis is **reduced** in the sense of (7):
--   $$\prod_{i=1}^n |b_i| \le c_2 \cdot d(L).$$
--   Let $h$ be the distance of $b_n$ to the hyperplane $H = \sum_{i=1}^{n-1}\mathbb R b_i$. Then
--   $$c_2^{-1}\cdot|b_n| \le h \le |b_n|.$$
--
--   The upper bound is (9), "clearly $h \le |b_n|$". The paper derives the lower bound from the chain
--   $$\prod_{i=1}^n |b_i| \le c_2\cdot d(L) = c_2\cdot h\cdot d(L') \le c_2 \cdot h \cdot \prod_{i=1}^{n-1}|b_i|,$$
--   using (7), (11), and Hadamard's inequality (6) applied to $L'$. Together the two bounds say that the layers $H + kb_n$ of the lattice are spaced at a distance comparable to $|b_n|$, which is what limits the number of layers that can meet a ball.
--
--   **Formalization Note** $c_2$ is any real number ("a constant only depending on $n$" in the paper); under the hypotheses it is automatically positive, since both sides of (7) are positive. The maximality of $|b_n|$ is not needed and not assumed. $n = k + 1$, $b_n$ is `b (Fin.last k)`, $d(L)$ is `latDet b` $= |\det(b_1,\dots,b_n)|$, $h$ is `hgt b`.
-- source:
--   Lenstra, Integer Programming with a Fixed Number of Variables, Math. Oper. Res. 8 (1983), §1, pp. 540–541, (9) and (12)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_LenstraIP_Hyperplanes_LatticeData

open KannanLattice.Core

namespace LenstraIP.Hyperplanes

/-- Lenstra (1983), §1, pp. 540–541, (12): for a basis with `∏ |bᵢ| ≤ c₂ · d(L)` (7),
`c₂⁻¹ · |bₙ| ≤ h ≤ |bₙ|`, where `h` is the distance of `bₙ` to `H = Σ_{i<n} ℝ bᵢ`. -/
theorem hgt_bounds (k : ℕ) (b : Fin (k + 1) → EuclideanSpace ℝ (Fin (k + 1)))
    (hb : LinearIndependent ℝ b) (c₂ : ℝ) (h7 : ∏ i, ‖b i‖ ≤ c₂ * latDet b) :
    c₂⁻¹ * ‖b (Fin.last k)‖ ≤ hgt b ∧ hgt b ≤ ‖b (Fin.last k)‖ := by sorry

end LenstraIP.Hyperplanes
