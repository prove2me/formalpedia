-- Prove2me | Theorems.Thm_HarlowTASI_entanglement_wedge_reconstruction
-- name    : HarlowTASI.entanglement_wedge_reconstruction
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:15:12.327991+00:00
-- url     : https://prove2.me/theorems/18456c4f-5ca9-4b05-bafd-ab344ac14800
-- title:
--   Theorem 5.2 — entanglement wedge reconstruction ⇔ quantum RT formula ⇔ JLMS formula
-- statement:
--   Let $\mathcal H=\mathcal H_R\otimes\mathcal H_{\overline R}$ be a finite-dimensional Hilbert space, let $\mathcal H_{code}\subseteq\mathcal H$ be a subspace, and let $M$ be a von Neumann algebra on $\mathcal H_{code}$ with commutant $M'$ and center $Z_M$. For a state $\tilde\rho$ on $\mathcal H_{code}$ write $\tilde\rho_R,\tilde\rho_{\overline R}$ for its reductions to $R$ and $\overline R$, and $S(\tilde\rho,M)$, $S(\tilde\rho|\tilde\sigma,M)$ for the algebraic entropy (5.16) and relative entropy (5.18). Then the following three statements are equivalent:
--
--   1. **Subregion duality.** For all $\tilde O\in M$ and $\tilde O'\in M'$ there are $O_R\in\mathcal L(\mathcal H_R)$ and $O'_{\overline R}\in\mathcal L(\mathcal H_{\overline R})$ such that for all $|\tilde\psi\rangle\in\mathcal H_{code}$
--   $$O_R|\tilde\psi\rangle=\tilde O|\tilde\psi\rangle,\quad O_R^\dagger|\tilde\psi\rangle=\tilde O^\dagger|\tilde\psi\rangle,\quad O'_{\overline R}|\tilde\psi\rangle=\tilde O'|\tilde\psi\rangle,\quad O'^\dagger_{\overline R}|\tilde\psi\rangle=\tilde O'^\dagger|\tilde\psi\rangle.\tag{5.19}$$
--   2. **Quantum RT formula.** There is an operator $\mathcal L_R\in Z_M$ such that for every state $\tilde\rho$ on $\mathcal H_{code}$
--   $$S(\tilde\rho_R)=\mathrm{Tr}(\tilde\rho\mathcal L_R)+S(\tilde\rho,M),\qquad S(\tilde\rho_{\overline R})=\mathrm{Tr}(\tilde\rho\mathcal L_R)+S(\tilde\rho,M').\tag{5.20}$$
--   3. **JLMS formula.** For all states $\tilde\rho,\tilde\sigma$ on $\mathcal H_{code}$
--   $$S(\tilde\rho_R|\tilde\sigma_R)=S(\tilde\rho|\tilde\sigma,M),\qquad S(\tilde\rho_{\overline R}|\tilde\sigma_{\overline R})=S(\tilde\rho|\tilde\sigma,M').\tag{5.21}$$
--
--   The theorem (proved in Harlow, *The Ryu–Takayanagi formula from quantum error correction*, 2017) shows that subregion duality in the entanglement wedge, the quantum Ryu–Takayanagi formula with a central area operator, and the JLMS formula are mathematically equivalent; the lectures name it as their main target. It does not assert that any of the three statements holds.
--
--   **Formalization Note** $\mathcal H_{code}$ is the image of an isometry $V:\mathbb C^C\to\mathbb C^{R\times\overline R}$, states on it are $C\times C$ density matrices $\tilde\rho$ (embedded as $V\tilde\rho V^\dagger$), and $O_R$ acts as $O_R\otimes I_{\overline R}$. $M$ is a $*$-subalgebra of $C\times C$ matrices; the algebraic entropies are evaluated in an arbitrary block decomposition $U$ of $M$ (Theorem 5.1 guarantees one exists; the entropies do not depend on the choice). The RT identity is stated in $\mathbb C$, so it also forces $\mathrm{Tr}(\tilde\rho\mathcal L_R)$ to be real; relative entropies are compared in the extended reals, so the value $+\infty$ is allowed on both sides.
-- source:
--   Daniel Harlow, TASI Lectures on the Emergence of Bulk Physics in AdS/CFT, PoS(TASI2017)002 (2018), arXiv:1802.01040, §5.3, pp. 45–46, Theorem 5.2, eqs. (5.19)–(5.21), with the entropies of eqs. (5.14)–(5.18).

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker

namespace HarlowTASI
theorem entanglement_wedge_reconstruction {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ) (hV : IsIsometry V)
    (M : StarSubalgebra ℂ (Matrix C C ℂ))
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U) (hMU : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U) :
    List.TFAE
      [ ∀ O ∈ M, ∀ O' ∈ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
          ∃ (OR : Matrix R R ℂ) (ORb : Matrix Rb Rb ℂ),
            (OR ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * O ∧
            (ORᴴ ⊗ₖ (1 : Matrix Rb Rb ℂ)) * V = V * Oᴴ ∧
            ((1 : Matrix R R ℂ) ⊗ₖ ORb) * V = V * O' ∧
            ((1 : Matrix R R ℂ) ⊗ₖ ORbᴴ) * V = V * O'ᴴ,
        ∃ L ∈ M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)),
          ∀ ρ : Matrix C C ℂ, IsDensityMatrix ρ →
            ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
                (ρ * L).trace + ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
            ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
                (ρ * L).trace + ((algebraicEntropyRight U ρ : ℝ) : ℂ),
        ∀ ρ σ : Matrix C C ℂ, IsDensityMatrix ρ → IsDensityMatrix σ →
          relativeEntropy (traceRight (V * ρ * Vᴴ)) (traceRight (V * σ * Vᴴ)) =
              algebraicRelEntropyLeft U ρ σ ∧
          relativeEntropy (traceLeft (V * ρ * Vᴴ)) (traceLeft (V * σ * Vᴴ)) =
              algebraicRelEntropyRight U ρ σ ] := by sorry
end HarlowTASI
