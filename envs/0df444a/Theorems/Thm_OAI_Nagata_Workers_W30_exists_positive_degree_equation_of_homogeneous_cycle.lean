-- Prove2me | Theorems.Thm_OAI_Nagata_Workers_W30_exists_positive_degree_equation_of_homogeneous_cycle
-- name    : OAI.Nagata.Workers.W30.exists_positive_degree_equation_of_homogeneous_cycle
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.457594+00:00
-- url     : https://prove2.me/theorems/4e1f30ca-71a6-4343-b765-f42b8bf48600
-- statement:
--   The theorem states that, in the ring of polynomials in three variables over the complex numbers, every nonzero finitely supported formal ℕ-combination of ideals (a cycle) whose support consists only of nonzero, prime, principal, homogeneous ideals (homogeneous for the standard grading by total degree) is the equation cycle of some polynomial. Here the equation cycle of a polynomial f is obtained from its factorization into irreducible factors up to associates: each associate class is replaced by the principal ideal it generates, with the class's multiplicity in f as coefficient. Precisely, for any such nonzero cycle there exists a polynomial f in ℂ[x₀,x₁,x₂] with f ≠ 0, f homogeneous of degree equal to its total degree, total degree of f strictly positive, and equationIdealCycle(f) equal to the given cycle.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Nagata.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Nagata.lean; bytes 7378..7912
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
import Definitions.Def_Nagata

namespace OAI

noncomputable section

open scoped BigOperators

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

local instance : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_positive_degree_equation_of_homogeneous_cycle
    (cycle : Ideal TernaryPolynomial →₀ ℕ) (nonzero : cycle ≠ 0)
    (homogeneous : ∀ ideal ∈ cycle.support,
      ideal.IsPrime ∧ ideal ≠ ⊥ ∧ ideal.IsPrincipal ∧
        ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ polynomial : TernaryPolynomial,
      polynomial ≠ 0 ∧ polynomial.IsHomogeneous polynomial.totalDegree ∧
        0 < polynomial.totalDegree ∧ equationIdealCycle polynomial = cycle := by
  sorry

end Nagata.Workers.W30
end
end OAI
