-- Prove2me | Theorems.Thm_HarlowTASI_blockAlgebraLeft_inter_right
-- name    : HarlowTASI.blockAlgebraLeft_inter_right
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T15:19:40.934974+00:00
-- url     : https://prove2.me/theorems/0c1e625c-1824-419f-8a3d-677089c8bd0b
-- title:
--   The center of $igoplus_lpha L(\mathcal H_{r_lpha})\otimes I$ consists of the block scalars
-- statement:
--   Let $U:\mathbb C^{C}\to\bigoplus_{\alpha<N}\mathbb C^{d_{r_\alpha}}\otimes\mathbb C^{d_{\overline r_\alpha}}$ be unitary. Then
--   $$\Big\{U^\dagger\Big(\bigoplus_\alpha x_\alpha\otimes I_{\overline r_\alpha}\Big)U\Big\}\ \cap\ \Big\{U^\dagger\Big(\bigoplus_\alpha I_{r_\alpha}\otimes y_\alpha\Big)U\Big\}=\Big\{U^\dagger\Big(\bigoplus_\alpha \lambda_\alpha I_{r_\alpha\overline r_\alpha}\Big)U\ :\ \lambda_\alpha\in\mathbb C\Big\},$$
--   where $x_\alpha$, $y_\alpha$ range over all complex matrices of sizes $d_{r_\alpha}$ and $d_{\overline r_\alpha}$. In other words, an operator of the form $x\otimes I$ that is also of the form $I\otimes y$ is a multiple of the identity in each block. Together with the commutant computation this gives the center $Z_M=\bigoplus_\alpha\lambda_\alpha I_{r_\alpha\overline r_\alpha}$ in (5.13).
-- source:
--   Center formula Z_M in eq. (5.13) of D. Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3, p. 44 (Theorem 5.1); cf. arXiv:1607.03901, Appendix A.6, p. 49 (Proposition A.7: Z_M is spanned by the block projections p_alpha).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

theorem blockAlgebraLeft_inter_right {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) :
    blockAlgebraLeft U ∩ blockAlgebraRight U = blockAlgebraCenter U := by sorry

end HarlowTASI
