-- Prove2me | Theorems.Thm_LefebvreVariations_hermite_constant_seven
-- name    : LefebvreVariations.hermite_constant_seven
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:25:24.938924+00:00
-- url     : https://prove2.me/theorems/ebc222dc-3331-4e17-8937-fd1e687c1933
-- title:
--   Lefebvre's variations, No. 161 — on a theme by Hermite: Hermite's constant γ₇ = 64^(1/7) (Blichfeldt)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the value of Hermite's constant $\gamma_7$ in dimension $7$, written for lattices given by a basis.
--
--   For every basis $b_1,\dots,b_7$ of $\mathbb{R}^7$ there is a nonzero $z \in \mathbb{Z}^7$ such that
--   $$\Bigl\|\sum_i z_i b_i\Bigr\|^{14} \;\le\; 64\,\bigl|\det(b_1,\dots,b_7)\bigr|^2 .$$
--   Equivalently, with $\Lambda = \bigoplus \mathbb{Z} b_i$ and $\operatorname{covol}\Lambda = |\det|$: every lattice in $\mathbb{R}^7$ has a nonzero vector $v$ with $\|v\|^2 \le \gamma_7\operatorname{covol}(\Lambda)^{2/7}$, where $\gamma_7^{7} = 64$ ($\gamma_7 = 64^{1/7}$). The constant is sharp: equality holds for the lattice $E_7$ (minimal squared length $2$, covolume $\sqrt2$).
--
--   Consequence: a lattice packing of unit balls in $\mathbb{R}^7$ has density at most $\pi^3/105$ (the density of $E_7$); this is how the statement relates to sphere packing, and the Lean bridge proves exactly this implication.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 7)`, whose norm is the Euclidean one. The lattice is given by a basis `b : Module.Basis (Fin 7) ℝ _` (it spans), its covolume is `|det|` of the basis in the standard orthonormal basis, and the lattice points are `∑ i, z i • b i` with `z : Fin 7 → ℤ`. To avoid roots, the inequality $\|v\|^2 \le \gamma_7\operatorname{covol}^{2/7}$ is raised to the power $7$ and written as $(\|v\|^2)^7 = \|v\|^{14} \le \gamma_7^{7}\operatorname{covol}^2$ with $\gamma_7^{7} = 64$.
--
--   **Why this is a Lefebvre variation.** It is the lattice case of the open statement `SpherePackingBeyond.dim7_optimal` ($\Delta_7 = \pi^3/105$, Conway–Sloane 1995), and not a reduction of it. A Lean-verified bridge proves that this statement implies $\Delta^L_7 \le \pi^3/105$, i.e. the lattice-packing version of the upper bound (`latticePackingConstant 7 ≤ ENNReal.ofReal (...)`), using a Lean proof that a lattice packing has density $\operatorname{vol}B(0,1)/\operatorname{covol}$ and Gamma-function values of the ball volume. The base statement does not follow from it: going from lattices to arbitrary packings is exactly the open part. It is the lattice case of the upper half of that equality (the lower half is the density of $E_7$). It was proved by Blichfeldt in 1935.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). H. F. Blichfeldt, The minimum values of positive quadratic forms in six, seven and eight variables, Math. Z. 39 (1935), 1–15 (γ_7 = 64^{1/7}). J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, Ch. 1 and Table 1.2 (Δᴸ_7 = π³/105). Origin of this statement: it is the lattice case of the upper bound of SpherePackingBeyond.dim7_optimal ($\Delta_7 = \pi^3/105$, Conway–Sloane 1995). A Lean-verified bridge (not a reduction of that statement) shows that it implies latticePackingConstant 7 ≤ ofReal(pi^3/105): a lattice packing has upper density vol B(0,1)/covolume (via Mathlib's lattice-point count), and the minimal vector bound then bounds the covolume from below.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LefebvreVariations
theorem hermite_constant_seven :
    ∀ b : Module.Basis (Fin 7) ℝ (EuclideanSpace ℝ (Fin 7)),
      ∃ z : Fin 7 → ℤ, z ≠ 0 ∧
        ‖∑ i, z i • b i‖ ^ 14 ≤
          (64 : ℝ) * |(EuclideanSpace.basisFun (Fin 7) ℝ).toBasis.det b| ^ 2 := by sorry
end LefebvreVariations
