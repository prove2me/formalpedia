-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_sec_mul
-- name    : GlobalTheory.DenseClosedAffineSubsets.sec_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:43:36.428657+00:00
-- url     : https://prove2.me/theorems/978a0da3-6f57-40c2-aae2-3f762a90bedd
-- title:
--   Dense Closed Affine Subsets: sec mul
-- statement:
--   The Dense Closed Affine Subsets construction uses the sec mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L174-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L174-L211

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.DenseClosedAffineSubsets.sec_mul {A : Type} [CommRing A] {σ : Type} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {t t' : A} (ht : t ∈ 𝒜 1) (ht' : t' ∈ 𝒜 1)
    {U : Scheme.{0}} (F : A →+* Γ(U, ⊤)) :
    (Proj.toBasicOpenOfGlobalSections 𝒜 F rfl one_pos ht).appTop
      (sec 𝒜 t (HomogeneousLocalization.Away.isLocalizationElem ht ht')) *
      (U.basicOpen (F t)).ι.appTop (F t) = (U.basicOpen (F t)).ι.appTop (F t') := by sorry
