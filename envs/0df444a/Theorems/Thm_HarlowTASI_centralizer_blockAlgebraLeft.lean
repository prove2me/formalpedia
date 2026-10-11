-- Prove2me | Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft
-- name    : HarlowTASI.centralizer_blockAlgebraLeft
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-10T15:19:15.324393+00:00
-- url     : https://prove2.me/theorems/e2d222ed-1ce5-4535-b61c-10e8eb53ae34
-- title:
--   The commutant of $igoplus_lpha L(\mathcal H_{r_lpha})\otimes I$ is $igoplus_lpha I\otimes L(\mathcal H_{\overline r_lpha})$
-- statement:
--   Let $U:\mathbb C^{C}\to\bigoplus_{\alpha<N}\mathbb C^{d_{r_\alpha}}\otimes\mathbb C^{d_{\overline r_\alpha}}$ be unitary, and let
--   $$\mathcal L=\Big\{U^\dagger\Big(\bigoplus_\alpha x_\alpha\otimes I_{\overline r_\alpha}\Big)U\Big\},\qquad \mathcal R=\Big\{U^\dagger\Big(\bigoplus_\alpha I_{r_\alpha}\otimes y_\alpha\Big)U\Big\},$$
--   where $x_\alpha$ and $y_\alpha$ range over all $d_{r_\alpha}\times d_{r_\alpha}$ and $d_{\overline r_\alpha}\times d_{\overline r_\alpha}$ complex matrices. Then the commutant of $\mathcal L$ in the $C\times C$ complex matrices is $\mathcal R$:
--   $$\mathcal L'=\{Y:\ YX=XY\ \text{for all }X\in\mathcal L\}=\mathcal R .$$
--   This is the computation "by studying the commutator of an arbitrary matrix with $a_i^\dagger a_j$" at the end of the proof of Theorem A.5, carried out block by block as in Theorem A.6.
-- source:
--   Step in the proof of Theorem 5.1 of D. Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3, p. 44, whose proof is deferred to D. Harlow, The Ryu-Takayanagi Formula from Quantum Error Correction, arXiv:1607.03901, Appendix A.5-A.6, pp. 47-49 (last sentence of the proof of Theorem A.5 and the statement of Theorem A.6: M' = direct sum of I tensor L(H_rbar)).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

theorem centralizer_blockAlgebraLeft {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) :
    Set.centralizer (blockAlgebraLeft U) = blockAlgebraRight U := by sorry

end HarlowTASI
