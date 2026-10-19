-- Prove2me | Theorems.Thm_MazurTransfer_ProperRelativeGroupTorsionSpecialization_eq_one_of_pow_eq_one_of_residue_specialization_eq_one
-- name    : MazurTransfer.ProperRelativeGroupTorsionSpecialization.eq_one_of_pow_eq_one_of_residue_specialization_eq_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T09:45:27.015106+00:00
-- url     : https://prove2.me/theorems/60772f8b-af77-4a0a-89f3-6a5f9d35aedb
-- title:
--   Proper relative group specialization detects torsion of invertible order
-- statement:
--   Let $R$ be a commutative ring, let $B$ be a local valuation domain with fraction field $K$, and let $t:\operatorname{Spec}B\to\operatorname{Spec}R$. Let $X/R$ be proper and carry a commutative relative group law $L$. For a natural number $m$ that is a unit in $B$, the actual specialization homomorphism to the residue field $\kappa(B)$ satisfies $$a^m=1\quad\text{and}\quad\operatorname{sp}(a)=1\quad\Longrightarrow\quad a=1$$ for every relative fraction-field point $a$. Properness defines specialization through unique integral extension. This detects torsion of invertible order and supplies the local geometric input for rational Picard torsion bounds.
-- source:
--   Original complete eq_one_of_pow_eq_one_of_residue_specialization_eq_one contract and full proof body from MazurTheorem ProperRelativeGroupTorsionSpecialization.lean, Apache-2.0, Vas and contributors. The main statement and proof body are unchanged; the four-line point_pow_eq_nsmul helper remains inside the solution under a fresh namespace. The public statement preamble includes only type dependencies. Complete original/public closed types are kernel-compared; native, strict and full frontend checks pass with standard axioms only. Reuses the original official Anthropic FLT relative-group residue torsion kernel at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: actual rational Picard torsion detection for the order-thirteen curve.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Uses official Anthropic FLT at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: invertible-order torsion detection by the actual residue
specialization of any proper relative group over a valuation ring.
Named downstream consumer: actual rational order-thirteen Picard torsion. -/
import Definitions.Def_MazurTransfer_ProperRelativeGroupValuationSpecialization
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open MazurTransfer.ValuationRingProperPointRestriction
open MazurTransfer.ProperRelativeGroupValuationSpecialization
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
variable (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B] [IsLocalRing B]
variable [Field K] [Algebra B K] [IsFractionRing B K]

theorem MazurTransfer.ProperRelativeGroupTorsionSpecialization.eq_one_of_pow_eq_one_of_residue_specialization_eq_one
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) [IsProper f]
    (t : Spec (.of B) ⟶ Spec (.of R)) (m : ℕ) (hm : IsUnit (m : B)) :
    letI := L.pointGroup (fractionInclusion B K ≫ t)
    letI := L.pointGroup (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)) ≫ t)
    ∀ a : SchemeHomOver (fractionInclusion B K ≫ t) f, a ^ m = 1 →
      specializationHom B K L t (IsLocalRing.ResidueField B) (IsLocalRing.residue B) a = 1 → a = 1 := by sorry
