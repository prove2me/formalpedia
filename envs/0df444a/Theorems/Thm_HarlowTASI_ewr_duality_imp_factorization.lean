-- Prove2me | Theorems.Thm_HarlowTASI_ewr_duality_imp_factorization
-- name    : HarlowTASI.ewr_duality_imp_factorization
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-26T20:29:38.453783+00:00
-- url     : https://prove2.me/theorems/74869d26-09ea-4e7d-a1b0-baede5b7f679
-- title:
--   Subregion duality implies the factorized form of the code
-- statement:
--   Let $\mathcal H_R,\mathcal H_{\overline R}$ be finite-dimensional, let $V:\mathbb C^C\to\mathcal H_R\otimes\mathcal H_{\overline R}$ be an isometry whose image is the code subspace, and let $U:\mathbb C^C\to\bigoplus_\alpha \mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}$ be a unitary, with $\dim\mathcal H_{r_\alpha}=d_\alpha$, $\dim\mathcal H_{\overline r_\alpha}=\overline d_\alpha$; write $|\alpha,i,j\rangle$ for the induced orthonormal basis of the code space. Let $M=U^\dagger\big(\bigoplus_\alpha\mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha}\big)U$ be the corresponding von Neumann algebra on the code space, with commutant $M'$. Assume **subregion duality** (5.19): every $\tilde O\in M$ is represented on the code space by some $O_R\otimes I_{\overline R}$ (together with its adjoint), and every $\tilde O'\in M'$ by some $I_R\otimes O'_{\overline R}$ (together with its adjoint). Then the code factorizes: there are finite-dimensional spaces $\mathcal H_{R_2^\alpha},\mathcal H_{\overline R_2^\alpha}$, unit vectors $|\chi_\alpha\rangle\in\mathcal H_{R_2^\alpha}\otimes\mathcal H_{\overline R_2^\alpha}$ (for each block with $d_\alpha,\overline d_\alpha>0$), and isometries $W_R:\bigoplus_\alpha\mathcal H_{r_\alpha}\otimes\mathcal H_{R_2^\alpha}\to\mathcal H_R$, $W_{\overline R}:\bigoplus_\alpha\mathcal H_{\overline R_2^\alpha}\otimes\mathcal H_{\overline r_\alpha}\to\mathcal H_{\overline R}$ such that
--   $$V\,U^\dagger|\alpha,i,j\rangle=(W_R\otimes W_{\overline R})\big(|\alpha,i\rangle_{r_\alpha}|\chi_\alpha\rangle_{R_2^\alpha\overline R_2^\alpha}|\alpha,j\rangle_{\overline r_\alpha}\big).$$
--
--   This is Harlow's structure theorem for codes with complementary recovery (the decomposition $\mathcal H_R=\bigoplus_\alpha\mathcal H_{R_1^\alpha}\otimes\mathcal H_{R_2^\alpha}\oplus\mathcal H_{R_3}$), the key step of (1) ⇒ (2) in Theorem 5.2.
--
--   **Formalization Note.** $\mathcal H_{R_2^\alpha}=\mathbb C^{m_\alpha}$, $\mathcal H_{\overline R_2^\alpha}=\mathbb C^{\overline m_\alpha}$; $|\chi_\alpha\rangle$ is given by its coefficient matrix $\chi_\alpha$ ($m_\alpha\times\overline m_\alpha$), normalized as $\mathrm{Tr}(\chi_\alpha\chi_\alpha^\dagger)=1$ only for blocks with $d_\alpha,\overline d_\alpha>0$ (empty blocks do not meet the code space). The identity is stated entrywise for the matrix $VU^\dagger$.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, proof of Theorem 5.2, (1) ⇒ (2); D. Harlow, The Ryu–Takayanagi formula from quantum error correction, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901, §5 (decomposition (5.29)).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem ewr_duality_imp_factorization {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ) :
    ∃ (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
      (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
      (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ),
      IsIsometry WR ∧ IsIsometry WRb ∧ (∀ a, 0 < dr a → 0 < drb a → (χ a * (χ a)ᴴ).trace = 1) ∧
      ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩ := by sorry
end HarlowTASI
