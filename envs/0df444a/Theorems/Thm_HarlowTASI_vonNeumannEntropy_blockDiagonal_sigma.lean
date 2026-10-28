-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumannEntropy_blockDiagonal_sigma
-- name    : HarlowTASI.vonNeumannEntropy_blockDiagonal_sigma
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:45.089833+00:00
-- url     : https://prove2.me/theorems/6ccebaec-4bd0-4191-9ccc-830f986f1bd1
-- title:
--   Entropy of a block-diagonal Hermitian matrix
-- statement:
--   Throughout, $S(X)=-\sum_\lambda\lambda\log\lambda$ is the von Neumann entropy of a Hermitian matrix $X$, the sum running over its eigenvalues with multiplicity ($0\log 0=0$); on non-Hermitian input it is set to $0$. For finitely many Hermitian blocks $Y_a$ (of possibly different sizes),
--   $$S\Big(\bigoplus_a Y_a\Big)=\sum_a S(Y_a).$$
--   The spectrum of a block-diagonal matrix is the union of the spectra of its blocks.
-- source:
--   Standard; see e.g. M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press (2000), §11.3. Used in Harlow, TASI Lectures, arXiv:1802.01040, §5.3.

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem vonNeumannEntropy_blockDiagonal_sigma {ι : Type} [Fintype ι] [DecidableEq ι]
    {o : ι → Type} [∀ a, Fintype (o a)] [∀ a, DecidableEq (o a)]
    (Y : ∀ a, Matrix (o a) (o a) ℂ) (hY : ∀ a, (Y a).IsHermitian) :
    vonNeumannEntropy (blockDiagonal' Y) = ∑ a, vonNeumannEntropy (Y a) := by sorry
end HarlowTASI
