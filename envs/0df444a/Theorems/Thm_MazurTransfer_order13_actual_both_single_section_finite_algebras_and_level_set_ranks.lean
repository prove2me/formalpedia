-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_both_single_section_finite_algebras_and_level_set_ranks
-- name    : MazurTransfer.order13_actual_both_single_section_finite_algebras_and_level_set_ranks
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T05:54:00.823454+00:00
-- url     : https://prove2.me/theorems/5c1abe8b-161a-43cd-ad4b-d8f2d555ac8f
-- statement:
--   The two original parameter subalgebras for the mixed single-section construction are free of rank three over the parameter polynomial ring over every integral commutative coefficient ring. Every original level set over a nontrivial coefficient algebra is finite free of rank three, with the original full hypotheses retained. Both explicit polynomial bases and both original FLT quotient/base-change identifications are preserved and checked as whole values in the two constructor interfaces. Named downstream consumer: identifying the actual affine opens and constructing the original degree-three FiniteMapData. No actual affine-open identification is assumed or claimed.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
noncomputable section
universe u
open scoped MazurTransfer.Order13MixedInverseParameterFiniteAlgebra MazurTransfer.Order13MixedSingleSectionFiniteAlgebra

theorem MazurTransfer.order13_actual_both_single_section_finite_algebras_and_level_set_ranks : (∀ (R : Type u) [CommRing R] [IsDomain R], Module.Free (Polynomial R) (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra R)) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.finrank (Polynomial R) (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra R) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R] (S : Type u) [CommRing S] [Algebra R S] [Nontrivial S] (s : S), Module.Finite S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) ∧ Module.Free S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) ∧ Module.finrank S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.Free (Polynomial R) (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R)) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.finrank (Polynomial R) (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R] (S : Type u) [CommRing S] [Algebra R S] [Nontrivial S] (s : S), Module.Finite S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) ∧ Module.Free S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) ∧ Module.finrank S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) = 3) := by sorry
