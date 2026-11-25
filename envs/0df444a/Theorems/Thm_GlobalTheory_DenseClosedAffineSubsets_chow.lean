-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_chow
-- name    : GlobalTheory.DenseClosedAffineSubsets.chow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:04:36.248968+00:00
-- url     : https://prove2.me/theorems/2a050cdd-b6f6-4099-a453-f617be860ead
-- title:
--   Dense Closed Affine Subsets: chow
-- statement:
--   The Dense Closed Affine Subsets construction uses the chow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L355-L456
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L355-L456

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem GlobalTheory.DenseClosedAffineSubsets.chow (R : Type) [CommRing R] [IsNoetherianRing R] (W : Scheme)
    (f : W ⟶ Spec (CommRingCat.of R)) (hsep : IsSeparated f) (hft : LocallyOfFiniteType f)
    (hqc : QuasiCompact f) (hne : Nonempty W) :
    ∃ (W' : Scheme) (P : Scheme) (π : W' ⟶ W) (q : W' ⟶ P) (s : P ⟶ Spec (CommRingCat.of R))
      (U : W.Opens), IsProper π ∧ Set.Nonempty (U : Set W) ∧ IsIso (π ∣_ U) ∧ IsProjOver s ∧
        IsImmersion q ∧ q ≫ s = π ≫ f := by sorry
