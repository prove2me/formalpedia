-- Prove2me | Theorems.Thm_LefebvreVariations_hermite_constant_five
-- name    : LefebvreVariations.hermite_constant_five
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:24:38.262091+00:00
-- url     : https://prove2.me/theorems/88f3b557-6520-47b0-929a-46096d82b445
-- title:
--   Lefebvre's variations, No. 196 — on a theme by Hermite: Hermite's constant γ₅ = 8^(1/5) (Korkine–Zolotarev)
-- statement:
--   *Lefebvre's variations — posed by Erwan Lefebvre.*
--
--   This is the value of Hermite's constant $\gamma_5$ in dimension $5$, written for lattices given by a basis.
--
--   For every basis $b_1,\dots,b_5$ of $\mathbb{R}^5$ there is a nonzero $z \in \mathbb{Z}^5$ such that
--   $$\Bigl\|\sum_i z_i b_i\Bigr\|^{10} \;\le\; 8\,\bigl|\det(b_1,\dots,b_5)\bigr|^2 .$$
--   Equivalently, with $\Lambda = \bigoplus \mathbb{Z} b_i$ and $\operatorname{covol}\Lambda = |\det|$: every lattice in $\mathbb{R}^5$ has a nonzero vector $v$ with $\|v\|^2 \le \gamma_5\operatorname{covol}(\Lambda)^{2/5}$, where $\gamma_5^{5} = 8$ ($\gamma_5 = 8^{1/5}$). The constant is sharp: equality holds for the lattice $D_5$ (minimal squared length $2$, covolume $2$).
--
--   Consequence: a lattice packing of unit balls in $\mathbb{R}^5$ has density at most $\pi^2/(15\sqrt{2})$ (the density of $D_5$); this is how the statement relates to sphere packing, and the Lean bridge proves exactly this implication.
--
--   **Formalization Note** Points live in `EuclideanSpace ℝ (Fin 5)`, whose norm is the Euclidean one. The lattice is given by a basis `b : Module.Basis (Fin 5) ℝ _` (it spans), its covolume is `|det|` of the basis in the standard orthonormal basis, and the lattice points are `∑ i, z i • b i` with `z : Fin 5 → ℤ`. To avoid roots, the inequality $\|v\|^2 \le \gamma_5\operatorname{covol}^{2/5}$ is raised to the power $5$ and written as $(\|v\|^2)^5 = \|v\|^{10} \le \gamma_5^{5}\operatorname{covol}^2$ with $\gamma_5^{5} = 8$.
--
--   **Why this is a Lefebvre variation.** It is the lattice case of the open statement `SpherePackingBeyond.dim5_optimal` ($\Delta_5 = \pi^2/(15\sqrt2)$, Conway–Sloane 1995), and not a reduction of it. A Lean-verified bridge proves that this statement implies $\Delta^L_5 \le \pi^2/(15\sqrt{2})$, i.e. the lattice-packing version of the upper bound (`latticePackingConstant 5 ≤ ENNReal.ofReal (...)`), using a Lean proof that a lattice packing has density $\operatorname{vol}B(0,1)/\operatorname{covol}$ and Gamma-function values of the ball volume. The base statement does not follow from it: going from lattices to arbitrary packings is exactly the open part. It is the lattice case of the upper half of that equality (the lower half is the density of $D_5$). It was proved by Korkine and Zolotarev in 1877.
--
--   **Attribution.** Series *Lefebvre's variations*, posed by Erwan Lefebvre.
-- source:
--   Posed by Erwan Lefebvre (series Lefebvre's variations). A. Korkine and G. Zolotarev, Sur les formes quadratiques, Math. Ann. 11 (1877), 242–292 (γ_5 = 8^{1/5}). J. W. S. Cassels, An Introduction to the Geometry of Numbers, Ch. V and Appendix; J. H. Conway and N. J. A. Sloane, Sphere Packings, Lattices and Groups, Ch. 1 and Table 1.2 (Δᴸ_5 = π²/(15√2)). Origin of this statement: it is the lattice case of the upper bound of SpherePackingBeyond.dim5_optimal ($\Delta_5 = \pi^2/(15\sqrt2)$, Conway–Sloane 1995). A Lean-verified bridge (not a reduction of that statement) shows that it implies latticePackingConstant 5 ≤ ofReal(pi^2/(15sqrt{2})): a lattice packing has upper density vol B(0,1)/covolume (via Mathlib's lattice-point count), and the minimal vector bound then bounds the covolume from below.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace LefebvreVariations
theorem hermite_constant_five :
    ∀ b : Module.Basis (Fin 5) ℝ (EuclideanSpace ℝ (Fin 5)),
      ∃ z : Fin 5 → ℤ, z ≠ 0 ∧
        ‖∑ i, z i • b i‖ ^ 10 ≤
          (8 : ℝ) * |(EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.det b| ^ 2 := by sorry
end LefebvreVariations
