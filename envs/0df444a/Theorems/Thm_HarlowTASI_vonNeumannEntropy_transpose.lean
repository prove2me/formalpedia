-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumannEntropy_transpose
-- name    : HarlowTASI.vonNeumannEntropy_transpose
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:42.996976+00:00
-- url     : https://prove2.me/theorems/cddf0a96-b5bc-4770-8ebc-3b3224d364ba
-- title:
--   Entropy is invariant under transposition
-- statement:
--   Throughout, $S(X)=-\sum_\lambda\lambda\log\lambda$ is the von Neumann entropy of a Hermitian matrix $X$, the sum running over its eigenvalues with multiplicity ($0\log 0=0$); on non-Hermitian input it is set to $0$. For every square complex matrix $H$,
--   $$S(H^{T})=S(H).$$
--   $H^T$ is Hermitian exactly when $H$ is, and it has the same characteristic polynomial.
-- source:
--   Standard; see e.g. M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press (2000), §11.3. Used in Harlow, TASI Lectures, arXiv:1802.01040, §5.3.

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem vonNeumannEntropy_transpose {n : Type} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) : vonNeumannEntropy Hᵀ = vonNeumannEntropy H := by sorry
end HarlowTASI
