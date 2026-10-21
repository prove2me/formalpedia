-- Prove2me | Theorems.Thm_HarlowTASI_ewr_jlms_imp_duality
-- name    : HarlowTASI.ewr_jlms_imp_duality
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-20T21:05:57.415234+00:00
-- url     : https://prove2.me/theorems/b3e7a641-acf4-467a-aee6-77e50e7662e7
-- title:
--   Theorem 5.2, (3) ⇒ (1): the JLMS formula implies subregion duality
-- statement:
--   Setting (as in `HarlowTASI.entanglement_wedge_reconstruction`): finite sets $R,\overline R,C$; an isometry $V:\mathbb C^C\to\mathcal H_R\otimes\mathcal H_{\overline R}$ ($V^\dagger V=I$) embedding the code subspace; a $*$-subalgebra $M$ of $C\times C$ matrices, with commutant $M'$ and center $Z_M=M\cap M'$; and a unitary $U$ exhibiting the block decomposition $M=U^\dagger\big(\bigoplus_\alpha \mathcal L(\mathcal H_{r_\alpha})\otimes I_{\overline r_\alpha}\big)U$ (5.12). For a state $\tilde\rho$ on the code space, $\tilde\rho_R=\mathrm{Tr}_{\overline R}(V\tilde\rho V^\dagger)$ and $\tilde\rho_{\overline R}=\mathrm{Tr}_R(V\tilde\rho V^\dagger)$; $S(\tilde\rho,M)$, $S(\tilde\rho,M')$ are the algebraic entropies (5.16) and $S(\tilde\rho|\tilde\sigma,M)$, $S(\tilde\rho|\tilde\sigma,M')$ the algebraic relative entropies (5.18), computed in this block decomposition (relative entropies take values in $[0,+\infty]$).
--
--   If **(3) JLMS formula**: for all density matrices $\tilde\rho,\tilde\sigma$ on the code space, $S(\tilde\rho_R|\tilde\sigma_R)=S(\tilde\rho|\tilde\sigma,M)$ and $S(\tilde\rho_{\overline R}|\tilde\sigma_{\overline R})=S(\tilde\rho|\tilde\sigma,M')$ (eq. 5.21), then **(1) subregion duality**: for every $\tilde O\in M$ and $\tilde O'\in M'$ there are $O_R$ on $\mathcal H_R$ and $O'_{\overline R}$ on $\mathcal H_{\overline R}$ with $(O_R\otimes I)V=V\tilde O$, $(O_R^\dagger\otimes I)V=V\tilde O^\dagger$, $(I\otimes O'_{\overline R})V=V\tilde O'$, $(I\otimes O'^\dagger_{\overline R})V=V\tilde O'^\dagger$ (eq. 5.19).
--
--   Together with the other two implications of the cycle (1) ⇒ (2) ⇒ (3) ⇒ (1), this gives Theorem 5.2.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, pp. 45–46, Theorem 5.2 and its proof, eqs. (5.19)–(5.21); see also D. Harlow, The Ryu–Takayanagi formula from quantum error correction, Commun. Math. Phys. 354 (2017) 865, arXiv:1607.03901.

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem ewr_jlms_imp_duality {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U)
    (h : ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
        relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
            algebraicRelEntropyLeft U ρ σ ∧
        relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
            algebraicRelEntropyRight U ρ σ) :
    ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
        ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
          (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
          (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
          ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ := by sorry
end HarlowTASI
