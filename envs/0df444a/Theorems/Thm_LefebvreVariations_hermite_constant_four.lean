-- Prove2me | Theorems.Thm_LefebvreVariations_hermite_constant_four
-- name    : LefebvreVariations.hermite_constant_four
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:24:11.213807+00:00
-- url     : https://prove2.me/theorems/a6083879-3017-4a30-987d-88641ae40491
-- title:
--   Lefebvre's variations: Hermite's constant γ₄ = √2 (Korkine–Zolotarev)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the value of Hermite's constant $\gamma_4$ in dimension $4$, written for lattices given by a basis.
--
--   For every basis $b_1,\dots,b_4$ of $\mathbb{R}^4$ there is a nonzero $z \in \mathbb{Z}^4$ such that
--   $$\Bigl\|\sum_i z_i b_i\Bigr\|^{8} \;\le\; 4\,\bigl|\det(b_1,\dots,b_4)\bigr|^2 .$$
--   Equivalently, with $\Lambda = \bigoplus \mathbb{Z} b_i$ and $\operatorname{covol}\Lambda = |\det|$: every lattice in $\mathbb{R}^4$ has a nonzero vector $v$ with $\|v\|^2 \le \gamma_4\operatorname{covol}(\Lambda)^{2/4}$, where $\gamma_4^{4} = 4$ ($\gamma_4 = \sqrt2$). The constant is sharp: equality holds for the lattice $D_4$ (minimal squared length $2$, covolume $2$).
--
--   Consequence: a lattice packing of unit balls in $\mathbb{R}^4$ has density at most $\pi^2/16$ (the density of $D_4$); this is how the statement relates to sphere packing, and the Lean bridge proves exactly this implication.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 4)`, whose norm is the Euclidean one. The lattice is given by a basis `b : Module.Basis (Fin 4) ℝ _` (it spans), its covolume is `|det|` of the basis in the standard orthonormal basis, and the lattice points are `∑ i, z i • b i` with `z : Fin 4 → ℤ`. To avoid roots, the inequality $\|v\|^2 \le \gamma_4\operatorname{covol}^{2/4}$ is raised to the power $4$ and written as $(\|v\|^2)^4 = \|v\|^{8} \le \gamma_4^{4}\operatorname{covol}^2$ with $\gamma_4^{4} = 4$.
--
--   **Why this is a Lefebvre variation.** It is the lattice case of the open statement `SpherePackingBeyond.dim4_upper` (every packing in $\mathbb{R}^4$ has density at most $\pi^2/16$, Conway–Sloane 1995), and not a reduction of it. A Lean-verified bridge proves that this statement implies $\Delta^L_4 \le \pi^2/16$, i.e. the lattice-packing version of the upper bound (`latticePackingConstant 4 ≤ ENNReal.ofReal (...)`), using a Lean proof that a lattice packing has density $\operatorname{vol}B(0,1)/\operatorname{covol}$ and Gamma-function values of the ball volume. The base statement does not follow from it: going from lattices to arbitrary packings is exactly the open part. It is also the lattice half of the upper bound needed for `SpherePackingBeyond.dim4_optimal`. It was proved by Korkine and Zolotarev in 1872–73.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). A. Korkine and G. Zolotarev, Sur les formes quadratiques positives quaternaires, Math. Ann. 5 (1872), 581–583, and Sur les formes quadratiques, Math. Ann. 6 (1873), 366–389 (γ_4 = √2). J. W. S. Cassels, An Introduction to the Geometry of Numbers, Ch. V and Appendix; J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, Ch. 1 and Table 1.2 (Δᴸ_4 = π²/16). Origin of this statement: it is the lattice case of the upper bound of SpherePackingBeyond.dim4_upper (every packing in $\mathbb{R}^4$ has density at most $\pi^2/16$, Conway–Sloane 1995). A Lean-verified bridge (not a reduction of that statement) shows that it implies latticePackingConstant 4 ≤ ofReal(pi^2/16): a lattice packing has upper density vol B(0,1)/covolume (via Mathlib's lattice-point count), and the minimal vector bound then bounds the covolume from below.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LefebvreVariations
theorem hermite_constant_four :
    ∀ b : Module.Basis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4)),
      ∃ z : Fin 4 → ℤ, z ≠ 0 ∧
        ‖∑ i, z i • b i‖ ^ 8 ≤
          (4 : ℝ) * |(EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.det b| ^ 2 := by sorry
end LefebvreVariations
