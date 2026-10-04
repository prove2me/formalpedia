-- Prove2me | Theorems.Thm_InfoDerivQT_states_are_density_matrices
-- name    : InfoDerivQT.states_are_density_matrices
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T17:09:33.888559+00:00
-- url     : https://prove2.me/theorems/fa52192e-095d-40db-bd89-f06027a35250
-- title:
--   Theorem 20 — the normalized states of every system are the density matrices on $\mathbb C^{d_A}$
-- statement:
--   Let $T$ be an operational-probabilistic theory satisfying causality, perfect distinguishability, ideal compression, local distinguishability, pure conditioning and purification, and let $A$ be a system. Then there are $n\in\mathbb N$ and a real-linear isomorphism $S$ from $\mathrm{St}_{\mathbb R}(A)$ onto the space of $n\times n$ complex Hermitian matrices such that
--
--   $$S\big(\mathrm{St}_1(A)\big)=\{M\in M_n(\mathbb C):\ M\succeq0,\ \operatorname{tr}M=1\},$$
--
--   and $n$ equals the size $N$ of every maximal set of perfectly distinguishable pure states of $A$ (the informational dimension $d_A$).
--
--   This is the paper's main result: the state space of every system is the set of density matrices on $\mathbb C^{d_A}$.
--
--   **Formalization Note** The Hermitian matrices are Mathlib's `selfAdjoint (Matrix (Fin n) (Fin n) ℂ)` as a real vector space; positivity is `Matrix.PosSemidef` with the standard order on $\mathbb C$.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-38, Sec. XIII, Theorem 20

import Mathlib
import Definitions.Def_InfoDerivQT_principles
open scoped ComplexOrder

namespace InfoDerivQT
theorem states_are_density_matrices (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys) :
    ∃ (n : ℕ) (S : Vec (T.size A) ≃ₗ[ℝ] selfAdjoint (Matrix (Fin n) (Fin n) ℂ)),
      (fun ρ => (S ρ : Matrix (Fin n) (Fin n) ℂ)) '' T.St1 A =
        {M | M.PosSemidef ∧ M.trace = 1} ∧
      ∀ (N : ℕ) (φ : Fin N → Vec (T.size A)), T.IsMaximalPerfDistPure A φ → N = n := by sorry
end InfoDerivQT
