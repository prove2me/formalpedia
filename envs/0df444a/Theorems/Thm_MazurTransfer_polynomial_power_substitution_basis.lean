-- Prove2me | Theorems.Thm_MazurTransfer_polynomial_power_substitution_basis
-- name    : MazurTransfer.polynomial_power_substitution_basis
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T11:07:20.948115+00:00
-- url     : https://prove2.me/theorems/f73b89ca-306e-4916-9fd3-203d35aa5817
-- title:
--   The polynomial power-substitution action has a basis of rank n
-- statement:
--   Let $R$ be a nontrivial commutative ring and let $n>0$. Give $R[X]$ the $R[T]$-module structure in which $T$ acts by multiplication by $X^n$. Then this module admits a basis indexed by $\mathrm{Fin}(n)$, so it is finite free of rank $n$. The formal statement explicitly specifies the algebra, scalar action and module structure of this substitution; this is necessary because both polynomial rings have the same underlying type. The result supplies the polynomial coefficient basis used to raise a curve parameter of degree $d$ to its $n$th power, of degree $nd$.
-- source:
--   Owned proof PolynomialPowerSubstitutionPresentation.lean and PolynomialPowerSubstitutionBasis.lean, part of the MazurTheorem campaign at https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Uses the literal monic presentation R[T][Y]/(Y^n-T) and Mathlib AdjoinRoot.powerBasis' at exact revision 0df444a360eaa60ab8c11dca51a86af692955474: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/AdjoinRoot.lean . Apache-2.0. Named consumer: actual whole order-13 finite-map data of degree 3n; the Mazur root statement is unchanged.

import Definitions.Def_MazurTransfer_PolynomialPowerSubstitution
import Mathlib

noncomputable section
universe u
open Polynomial Module

theorem MazurTransfer.polynomial_power_substitution_basis (R : Type u) [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : n ≠ 0) :
    letI : Algebra (Polynomial R) (Polynomial R) :=
      (aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra
    letI : SMul (Polynomial R) (Polynomial R) :=
      ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra).toSMul
    letI : Module (Polynomial R) (Polynomial R) :=
      @Algebra.toModule _ _ _ _ ((aeval ((X : Polynomial R)^n)).toRingHom.toAlgebra)
    Nonempty (Basis (Fin n) (Polynomial R) (Polynomial R)) := by sorry
