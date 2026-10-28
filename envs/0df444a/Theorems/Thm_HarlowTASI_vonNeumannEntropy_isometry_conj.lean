-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumannEntropy_isometry_conj
-- name    : HarlowTASI.vonNeumannEntropy_isometry_conj
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:46.90369+00:00
-- url     : https://prove2.me/theorems/86c5b6df-1cab-4cde-9fc5-6b4cc1c225ca
-- title:
--   Entropy is invariant under isometric embedding
-- statement:
--   Throughout, $S(X)=-\sum_\lambda\lambda\log\lambda$ is the von Neumann entropy of a Hermitian matrix $X$, the sum running over its eigenvalues with multiplicity ($0\log 0=0$); on non-Hermitian input it is set to $0$. If $W$ is an isometry ($W^\dagger W=I$), then for every square matrix $Y$
--   $$S(WYW^\dagger)=S(Y).$$
--   For Hermitian $Y$ the spectrum of $WYW^\dagger$ is that of $Y$ plus zeros; for non-Hermitian $Y$ both sides are $0$, because $Y=W^\dagger(WYW^\dagger)W$.
-- source:
--   Standard; see e.g. M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press (2000), §11.3. Used in Harlow, TASI Lectures, arXiv:1802.01040, §5.3.

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem vonNeumannEntropy_isometry_conj {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (W : Matrix m n ℂ) (hW : IsIsometry W) (Y : Matrix n n ℂ) :
    vonNeumannEntropy (W * Y * Wᴴ) = vonNeumannEntropy Y := by sorry
end HarlowTASI
