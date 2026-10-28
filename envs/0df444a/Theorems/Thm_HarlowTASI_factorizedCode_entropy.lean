-- Prove2me | Theorems.Thm_HarlowTASI_factorizedCode_entropy
-- name    : HarlowTASI.factorizedCode_entropy
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:29:30.781535+00:00
-- url     : https://prove2.me/theorems/b5c8281a-6b18-4903-a33d-9424d90e1f50
-- title:
--   Entropies of boundary regions for a factorized code
-- statement:
--   Let $\mathcal H_R,\mathcal H_{\overline R}$ be finite-dimensional, let $V:\mathbb C^C\to\mathcal H_R\otimes\mathcal H_{\overline R}$ be an isometry whose image is the code subspace, and let $U:\mathbb C^C\to\bigoplus_\alpha \mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}$ be a unitary, with $\dim\mathcal H_{r_\alpha}=d_\alpha$, $\dim\mathcal H_{\overline r_\alpha}=\overline d_\alpha$; write $|\alpha,i,j\rangle$ for the induced orthonormal basis of the code space. Suppose the code factorizes as
--   $$V\,U^\dagger|\alpha,i,j\rangle=(W_R\otimes W_{\overline R})\big(|\alpha,i\rangle|\chi_\alpha\rangle|\alpha,j\rangle\big)$$
--   with isometries $W_R,W_{\overline R}$ and unit vectors $|\chi_\alpha\rangle\in\mathcal H_{R_2^\alpha}\otimes\mathcal H_{\overline R_2^\alpha}$ (for the nonempty blocks). Then for every density matrix $\tilde\rho$ on the code space
--   $$S(\tilde\rho_R)=\mathrm{Tr}(\tilde\rho\,\mathcal L_R)+S(\tilde\rho,M),\qquad S(\tilde\rho_{\overline R})=\mathrm{Tr}(\tilde\rho\,\mathcal L_{\overline R})+S(\tilde\rho,M'),$$
--   where $\mathcal L_R=U^\dagger\big(\bigoplus_\alpha S(\chi_{\alpha,R_2})\,I_\alpha\big)U$, $\mathcal L_{\overline R}=U^\dagger\big(\bigoplus_\alpha S(\chi_{\alpha,\overline R_2})\,I_\alpha\big)U$, and $S(\tilde\rho,M),S(\tilde\rho,M')$ are the algebraic entropies (5.16) in the block decomposition $U$. This is the entropy computation in the proof of (1) ⇒ (2) of Theorem 5.2: the reduced state is $W_R\big(\bigoplus_\alpha p_\alpha\tilde\rho_{r_\alpha}\otimes\chi_{\alpha,R_2}\big)W_R^\dagger$.
--
--   **Formalization Note.** With $\chi_\alpha$ the coefficient matrix of $|\chi_\alpha\rangle$, $\chi_{\alpha,R_2}=\chi_\alpha\chi_\alpha^\dagger$ and the entropy of $\chi_{\alpha,\overline R_2}$ is that of $\chi_\alpha^\dagger\chi_\alpha$. The identities are stated in $\mathbb C$.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, proof of Theorem 5.2, (1) ⇒ (2); D. Harlow, The Ryu–Takayanagi formula from quantum error correction, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901, §5 (decomposition (5.29)).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem factorizedCode_entropy {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U)
    (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR) (hWRb : IsIsometry WRb) (hχ : ∀ a, 0 < dr a → 0 < drb a → (χ a * (χ a)ᴴ).trace = 1)
    (hVU : ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩)
    (ρ : Matrix C C ℂ) (hρ : IsDensityMatrix ρ) :
    ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb)
          (fun a => ((vonNeumannEntropy (χ a * (χ a)ᴴ) : ℝ) : ℂ)) * U)).trace +
        ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
    ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb)
          (fun a => ((vonNeumannEntropy ((χ a)ᴴ * χ a) : ℝ) : ℂ)) * U)).trace +
        ((algebraicEntropyRight U ρ : ℝ) : ℂ) := by sorry
end HarlowTASI
