-- Prove2me | Theorems.Thm_HarlowTASI_vonNeumannEntropy_kronecker
-- name    : HarlowTASI.vonNeumannEntropy_kronecker
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T20:49:44.416621+00:00
-- url     : https://prove2.me/theorems/22c25837-6b9e-4019-a032-e16d8237c70b
-- title:
--   Entropy of a tensor product
-- statement:
--   Throughout, $S(X)=-\sum_\lambda\lambda\log\lambda$ is the von Neumann entropy of a Hermitian matrix $X$, the sum running over its eigenvalues with multiplicity ($0\log 0=0$); on non-Hermitian input it is set to $0$. For Hermitian matrices $A$ and $B$,
--   $$S(A\otimes B)=\mathrm{Tr}(B)\,S(A)+\mathrm{Tr}(A)\,S(B).$$
--   For density matrices this is additivity $S(A\otimes B)=S(A)+S(B)$; the general form also covers unnormalized blocks $p\,\rho\otimes\chi$.
-- source:
--   Standard; see e.g. M. A. Nielsen and I. L. Chuang, Quantum Computation and Quantum Information, Cambridge University Press (2000), §11.3. Used in Harlow, TASI Lectures, arXiv:1802.01040, §5.3.

import Mathlib
import Definitions.Def_HarlowTASI_QuantumBasics

open Matrix
open scoped Kronecker ComplexOrder

namespace HarlowTASI
theorem vonNeumannEntropy_kronecker {p q : Type} [Fintype p] [DecidableEq p]
    [Fintype q] [DecidableEq q] (A : Matrix p p ℂ) (B : Matrix q q ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vonNeumannEntropy (A ⊗ₖ B) =
      B.trace.re * vonNeumannEntropy A + A.trace.re * vonNeumannEntropy B := by sorry
end HarlowTASI
