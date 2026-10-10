-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumann_block_decomposition
-- name    : HarlowTASI.vonNeumann_block_decomposition
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:13:18.209133+00:00
-- url     : https://prove2.me/theorems/9fe2493a-0053-4d71-adb3-50c74bbfb8c1
-- title:
--   Theorem 5.1 — every finite-dimensional von Neumann algebra is a block-diagonal direct sum of factors
-- statement:
--   Let $M$ be a von Neumann algebra on a finite-dimensional Hilbert space $\mathcal H$, i.e. a set of operators closed under sums, products and adjoints and containing every $\lambda I$ (Definition 5.3). Then there is a Hilbert space direct sum decomposition
--   $$\mathcal H=\bigoplus_\alpha\big(\mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}\big)\tag{5.12}$$
--   such that
--   $$M=\bigoplus_\alpha\big(\mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha}\big),\qquad M'=\bigoplus_\alpha\big(I_{r_\alpha}\otimes\mathcal L(\mathcal H_{\overline r_\alpha})\big),\qquad Z_M=\bigoplus_\alpha\lambda_\alpha I_{r_\alpha\overline r_\alpha},\tag{5.13}$$
--   where $M'$ is the commutant (Definition 5.4) and $Z_M=M\cap M'$ the center (Definition 5.5).
--
--   This structure theorem is what makes the algebraic entropy (5.16) and relative entropy (5.18) meaningful for an arbitrary von Neumann algebra, and it is the setting of Theorem 5.2.
--
--   **Formalization Note** $\mathcal H=\mathbb C^{C}$, $M$ is a $*$-subalgebra of the $C\times C$ complex matrices, the commutant is the centralizer, and the decomposition is a unitary $U:\mathbb C^C\to\bigoplus_{\alpha<N}\mathbb C^{d_{r_\alpha}}\otimes\mathbb C^{d_{\overline r_\alpha}}$ with all block dimensions positive.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, p. 44, Definitions 5.3–5.5 and Theorem 5.1, eqs. (5.12)–(5.13).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

namespace HarlowTASI
theorem vonNeumann_block_decomposition {C : Type} [Fintype C] [DecidableEq C]
    (M : StarSubalgebra ℂ (Matrix C C ℂ)) :
    ∃ (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ),
      IsUnitaryMatrix U ∧ (∀ a, 0 < dr a ∧ 0 < drb a) ∧
      (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U ∧
      (StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) : Set (Matrix C C ℂ)) =
        blockAlgebraRight U ∧
      ((M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) :
          StarSubalgebra ℂ (Matrix C C ℂ)) : Set (Matrix C C ℂ)) = blockAlgebraCenter U := by sorry
end HarlowTASI
