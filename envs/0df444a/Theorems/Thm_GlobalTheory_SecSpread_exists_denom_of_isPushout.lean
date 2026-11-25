-- Prove2me | Theorems.Thm_GlobalTheory_SecSpread_exists_denom_of_isPushout
-- name    : GlobalTheory.SecSpread.exists_denom_of_isPushout
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:08:01.974923+00:00
-- url     : https://prove2.me/theorems/fa570bd0-e8e9-5e04-8770-60d7274b87fe
-- title:
--   Sec Spread: exists denom of is Pushout
-- statement:
--   The Sec Spread construction uses the exists denom of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L14-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
open GlobalTheory GlobalTheory.SecSpread

theorem GlobalTheory.SecSpread.exists_denom_of_isPushout {R : Type} [CommRing R] [IsDomain R] {R₀ A K P : CommRingCat.{0}} {α : R₀ ⟶ A}
    {ψ : R₀ ⟶ K} {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout α ψ inl inr) (c : R →+* R₀)
    (hK : ∀ k : K, ∃ d : R, d ≠ 0 ∧ ∃ r : R₀, ψ.hom (c d) * k = ψ.hom r) (t : P) :
    ∃ d : R, d ≠ 0 ∧ ∃ a : A, inl.hom (α.hom (c d)) * t = inl.hom a := by sorry
