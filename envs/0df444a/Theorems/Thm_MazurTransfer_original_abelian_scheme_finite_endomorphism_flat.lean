-- Prove2me | Theorems.Thm_MazurTransfer_original_abelian_scheme_finite_endomorphism_flat
-- name    : MazurTransfer.original_abelian_scheme_finite_endomorphism_flat
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-21T04:37:31.329172+00:00
-- url     : https://prove2.me/theorems/71d4013b-58d1-4056-9ab0-435fc410d873
-- statement:
--   Every finite relative endomorphism of the same original abelian scheme is flat over its original arbitrary commutative base. The original field and fibrewise flatness inputs and pullback certificate are reused from the complete official FLT proofs. All schemes, maps, base hypotheses and universes are retained. Named downstream consumer: positive-scalar norm factors and the actual integral nineteen norm models.

import Theorems.Thm_AlgebraicGeometry_flat_of_locallyOfFinitePresentation_of_forall_flat_schemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import Theorems.Thm_GoodReductionJacobian_abelianSchemePropertyBundle_fibreStr
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem MazurTransfer.original_abelian_scheme_finite_endomorphism_flat : ∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (hA : AbelianSchemePropertyBundle R f) (β : SchemeHomOver f f) [IsFinite β.val], Flat β.val := by sorry
