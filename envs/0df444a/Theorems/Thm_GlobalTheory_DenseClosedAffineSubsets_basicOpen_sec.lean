-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_basicOpen_sec
-- name    : GlobalTheory.DenseClosedAffineSubsets.basicOpen_sec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:47.567389+00:00
-- url     : https://prove2.me/theorems/4834bf61-87af-4591-9194-b3ed9b78834a
-- title:
--   Dense Closed Affine Subsets: basic Open sec
-- statement:
--   The Dense Closed Affine Subsets construction uses the basic Open sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L162-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L162-L171

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

theorem GlobalTheory.DenseClosedAffineSubsets.basicOpen_sec {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1) :
    (Proj.basicOpen 𝒜 t).toScheme.basicOpen
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) =
      (Proj.basicOpen 𝒜 t).ι ⁻¹ᵁ Proj.basicOpen 𝒜 t' := by sorry
