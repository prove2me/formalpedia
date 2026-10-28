-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_normal_basis_separation_logarithmic_primitive
-- name    : OAI.PiExponent.FormalInterpolation.normal_basis_separation_logarithmic_primitive
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T23:20:25.90087+00:00
-- url     : https://prove2.me/theorems/44d294ec-843b-4881-8753-f2957f04181f
-- title:
--   Ordered normal-basis exclusion forces a logarithmic primitive
-- statement:
--   This is a finite-column linear-algebra step with no multiplicity estimate. Pick the largest positive nonzero coordinate normal column i and extend it to a basis. Higher columns vanish in both frames, so exclusion forces every frame basis to contain i. Consequently every relation among frame columns has coefficient i equal to zero. Applying a derivation to the equations in P supplies such a relation, with coefficients D(Y)/Y and D(X_j)−D(Y)/Y. Thus choose z=X_i. If every positive column vanishes, a minimal-degree nonzero equation shows the zeroth column is nonzero; the chain rule then gives D(Y)=0, and z=0 works. Nonzero P and Y outside P are essential retained boundary hypotheses.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.normal_basis_separation_logarithmic_primitive
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (hP : P ≠ ⊥) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hexclusion :
      ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
        coordinateNormalBasisAtPrime P A →
        logarithmicNormalBasisAtPrime P B →
        ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
          (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ z : logarithmicPrimeField P,
      ∀ D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P),
        D z =
          D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1)))) /
          algebraMap (MvPolynomial (Fin (m + 1)) Complex)
            (logarithmicPrimeField P) (MvPolynomial.X (0 : Fin (m + 1))) := by sorry
