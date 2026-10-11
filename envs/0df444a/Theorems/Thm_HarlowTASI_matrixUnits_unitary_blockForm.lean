-- Prove2me | Theorems.Thm_HarlowTASI_matrixUnits_unitary_blockForm
-- name    : HarlowTASI.matrixUnits_unitary_blockForm
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T15:18:44.934992+00:00
-- url     : https://prove2.me/theorems/1a91ccb4-7cdc-4cfa-b36e-88235f9959e4
-- title:
--   A complete system of matrix units is unitarily equivalent to $igoplus_lpha L(\mathcal H_{r_lpha})\otimes I_{\overline r_lpha}$
-- statement:
--   Let $e^{\alpha}_{ij}$ ($\alpha<N$, $0\le i,j<d_{r_\alpha}$) be $C\times C$ complex matrices satisfying
--   $$e^{\alpha}_{ij}\,e^{\alpha}_{kl}=\delta_{jk}\,e^{\alpha}_{il},\qquad e^{\alpha}_{ij}\,e^{\beta}_{kl}=0\ (\alpha\ne\beta),\qquad (e^{\alpha}_{ij})^\dagger=e^{\alpha}_{ji},\qquad e^{\alpha}_{ii}\neq 0,\qquad \sum_{\alpha}\sum_i e^{\alpha}_{ii}=I .$$
--   Then there are dimensions $d_{\overline r_\alpha}\ge1$ and a unitary $U:\mathbb C^{C}\to\bigoplus_{\alpha<N}\mathbb C^{d_{r_\alpha}}\otimes\mathbb C^{d_{\overline r_\alpha}}$ such that for every family of matrices $x^\alpha\in\mathbb C^{d_{r_\alpha}\times d_{r_\alpha}}$
--   $$U^\dagger\Big(\bigoplus_\alpha x^\alpha\otimes I_{d_{\overline r_\alpha}}\Big)U=\sum_\alpha\sum_{i,j}x^\alpha_{ij}\,e^{\alpha}_{ij}.$$
--
--   Concretely, $d_{\overline r_\alpha}$ is the rank of $e^\alpha_{00}$ and, for an orthonormal basis $f^\alpha_k$ of the range of $e^{\alpha}_{00}$, the vectors $e^{\alpha}_{i0}f^\alpha_k$ form an orthonormal basis of $\mathbb C^C$; this is the choice of basis in each block made at the end of the proof of Theorem A.5.
-- source:
--   Step in the proof of Theorem 5.1 of D. Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3, p. 44, whose proof is deferred to D. Harlow, The Ryu-Takayanagi Formula from Quantum Error Correction, arXiv:1607.03901, Appendix A.5-A.6, pp. 47-49 (proof of Theorem A.5: choosing a basis in each block so that a_i^dagger a_j is the (i,j) block unit tensored with the identity).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
open Matrix
open scoped Kronecker

theorem matrixUnits_unitary_blockForm {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} (dr : Fin N → ℕ) (e : (a : Fin N) → Fin (dr a) → Fin (dr a) → Matrix C C ℂ)
    (hmul : ∀ a i j k l, e a i j * e a k l = if j = k then e a i l else 0)
    (horth : ∀ a b i j k l, a ≠ b → e a i j * e b k l = 0)
    (hstar : ∀ a i j, (e a i j)ᴴ = e a j i)
    (hne : ∀ a i, e a i i ≠ 0)
    (hsum : ∑ a, ∑ i, e a i i = 1) :
    ∃ (drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ),
      IsUnitaryMatrix U ∧ (∀ a, 0 < drb a) ∧
      ∀ x : ∀ a, Matrix (Fin (dr a)) (Fin (dr a)) ℂ,
        Uᴴ * blockLeftOp (drb := drb) x * U = ∑ a, ∑ i, ∑ j, x a i j • e a i j := by sorry

end HarlowTASI
