-- Prove2me | Theorems.Thm_HarlowTASI_factorizedCode_reducedStates
-- name    : HarlowTASI.factorizedCode_reducedStates
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:43.142059+00:00
-- url     : https://prove2.me/theorems/448139e5-ce2e-442c-a5a5-dbd43d1c5cbf
-- title:
--   Reduced states of a factorized code
-- statement:
--   Let $V:\mathbb C^C\to\mathcal H_R\otimes\mathcal H_{\overline R}$ and let $U:\mathbb C^C\to\bigoplus_\alpha\mathcal H_{r_\alpha}\otimes\mathcal H_{\overline r_\alpha}$ be unitary. Suppose the code factorizes as
--   $$VU^\dagger|\alpha,i,j\rangle=(W_R\otimes W_{\overline R})\big(|\alpha,i\rangle|\chi_\alpha\rangle|\alpha,j\rangle\big),$$
--   with isometries $W_R:\bigoplus_\alpha\mathcal H_{r_\alpha}\otimes\mathcal H_{R_2^\alpha}\to\mathcal H_R$, $W_{\overline R}:\bigoplus_\alpha\mathcal H_{\overline R_2^\alpha}\otimes\mathcal H_{\overline r_\alpha}\to\mathcal H_{\overline R}$ and vectors $|\chi_\alpha\rangle=\sum_{k,l}(\chi_\alpha)_{kl}|k\rangle|l\rangle$. Then for every $\rho$ on $\mathbb C^C$, with $\rho_{\alpha\alpha}$ the diagonal block $\alpha$ of $U\rho U^\dagger$,
--   $$\mathrm{Tr}_{\overline R}(V\rho V^\dagger)=W_R\Big(\bigoplus_\alpha \mathrm{Tr}_{\overline r_\alpha}\rho_{\alpha\alpha}\otimes\chi_\alpha\chi_\alpha^\dagger\Big)W_R^\dagger,\qquad \mathrm{Tr}_{R}(V\rho V^\dagger)=W_{\overline R}\Big(\bigoplus_\alpha (\chi_\alpha^\dagger\chi_\alpha)^{T}\otimes\mathrm{Tr}_{r_\alpha}\rho_{\alpha\alpha}\Big)W_{\overline R}^\dagger.$$
--   This is the reduced-state formula $\tilde\rho_R=U_R\big(\bigoplus_\alpha p_\alpha\tilde\rho_{r_\alpha}\otimes\chi_{R_2^\alpha}\big)U_R^\dagger$ in Harlow's proof of (1) ⇒ (2) of Theorem 5.2.
--
--   **Formalization Note.** The factorization is stated entrywise for the matrix $VU^\dagger$; $\otimes$ is the Kronecker product and $\bigoplus$ is `blockDiagonal'`.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, arXiv:1802.01040, §5.3 (proof of Theorem 5.2, (1) ⇒ (2)); D. Harlow, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901, §5.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem factorizedCode_reducedStates {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U)
    (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR) (hWRb : IsIsometry WRb)
    (hVU : ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩)
    (ρ : Matrix C C ℂ) :
    traceRight (V * ρ * Vᴴ) =
        WR * blockDiagonal' (fun a => traceRight (diagBlock U ρ a) ⊗ₖ (χ a * (χ a)ᴴ)) * WRᴴ ∧
    traceLeft (V * ρ * Vᴴ) =
        WRb * blockDiagonal' (fun a => ((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U ρ a)) * WRbᴴ := by sorry
end HarlowTASI
