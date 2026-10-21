-- Prove2me | Theorems.Thm_HarlowTASI_ewr_rt_imp_jlms
-- name    : HarlowTASI.ewr_rt_imp_jlms
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-20T21:06:23.720621+00:00
-- url     : https://prove2.me/theorems/f45d2656-0437-4a29-ac00-348a38f721a7
-- title:
--   Theorem 5.2, (2) ⇒ (3): the quantum RT formula implies the JLMS formula
-- statement:
--   Setting (as in `HarlowTASI.entanglement_wedge_reconstruction`): finite sets $R,\overline R,C$; an isometry $V:\mathbb C^C\to\mathcal H_R\otimes\mathcal H_{\overline R}$ ($V^\dagger V=I$) embedding the code subspace; a $*$-subalgebra $M$ of $C\times C$ matrices, with commutant $M'$ and center $Z_M=M\cap M'$; and a unitary $U$ exhibiting the block decomposition $M=U^\dagger\big(\bigoplus_\alpha \mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha}\big)U$ (5.12). For a state $\tilde\rho$ on the code space, $\tilde\rho_R=\mathrm{Tr}_{\overline R}(V\tilde\rho V^\dagger)$ and $\tilde\rho_{\overline R}=\mathrm{Tr}_R(V\tilde\rho V^\dagger)$; $S(\tilde\rho,M)$, $S(\tilde\rho,M')$ are the algebraic entropies (5.16) and $S(\tilde\rho|\tilde\sigma,M)$, $S(\tilde\rho|\tilde\sigma,M')$ the algebraic relative entropies (5.18), computed in this block decomposition (relative entropies take values in $[0,+\infty]$).
--
--   If **(2) quantum RT formula**: there is $\mathcal L_R\in Z_M$ such that for every density matrix $\tilde\rho$ on the code space, $S(\tilde\rho_R)=\mathrm{Tr}(\tilde\rho\mathcal L_R)+S(\tilde\rho,M)$ and $S(\tilde\rho_{\overline R})=\mathrm{Tr}(\tilde\rho\mathcal L_R)+S(\tilde\rho,M')$ (eq. 5.20), then **(3) JLMS formula**: for all density matrices $\tilde\rho,\tilde\sigma$ on the code space, $S(\tilde\rho_R|\tilde\sigma_R)=S(\tilde\rho|\tilde\sigma,M)$ and $S(\tilde\rho_{\overline R}|\tilde\sigma_{\overline R})=S(\tilde\rho|\tilde\sigma,M')$ (eq. 5.21).
--
--   Together with the other two implications of the cycle (1) ⇒ (2) ⇒ (3) ⇒ (1), this gives Theorem 5.2.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, pp. 45–46, Theorem 5.2 and its proof, eqs. (5.19)–(5.21); see also D. Harlow, The Ryu–Takayanagi formula from quantum error correction, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem ewr_rt_imp_jlms {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∃ L ∈ M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
          ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
          ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
              (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ)) :
    ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
        relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
            algebraicRelEntropyLeft U ρ σ ∧
        relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
            algebraicRelEntropyRight U ρ σ := by sorry
end HarlowTASI
