-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumannEntropy_mul_conjTranspose_comm
-- name    : HarlowTASI.vonNeumannEntropy_mul_conjTranspose_comm
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:29:30.364742+00:00
-- url     : https://prove2.me/theorems/26545f7b-151b-485e-9c7a-9a2b5b7c624a
-- title:
--   Equal entropy of the two reduced states of a pure state
-- statement:
--   For any complex $m\times n$ matrix $A$, the von Neumann entropies (computed from eigenvalues, $S(X)=-\sum_\lambda\lambda\log\lambda$) of $AA^\dagger$ and $A^\dagger A$ agree:
--   $$S(AA^\dagger)=S(A^\dagger A).$$
--   Since $AA^\dagger$ and $A^\dagger A$ have the same nonzero eigenvalues, this is the statement that the two reduced states of a bipartite pure state $|\chi\rangle=\sum_{k,l}A_{kl}|k\rangle|l\rangle$ have equal entropy (Schmidt decomposition).
-- source:
--   Standard (Schmidt decomposition); used in D. Harlow, TASI Lectures, arXiv:1802.01040, §5.3.

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix

namespace HarlowTASI
theorem vonNeumannEntropy_mul_conjTranspose_comm {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (A : Matrix m n ℂ) :
    vonNeumannEntropy (A * Aᴴ) = vonNeumannEntropy (Aᴴ * A) := by sorry
end HarlowTASI
