-- Prove2me | Theorems.Thm_GlobalTheory_SecSpread_exists_glue
-- name    : GlobalTheory.SecSpread.exists_glue
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:02:52.98369+00:00
-- url     : https://prove2.me/theorems/61b051c6-d127-4fbb-b479-9e5fd0370da5
-- title:
--   Sec Spread: exists glue
-- statement:
--   The Sec Spread construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L92-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L92-L103

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
variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}

theorem GlobalTheory.SecSpread.exists_glue (H : IsPullback φ π p (spMap (algebraMap R K))) [Flat p] (W : X.Opens)
    (t : ∀ z : X', X'.presheaf.stalk z)
    (h : ∀ x ∈ W, ∃ (U : X.Opens) (_ : U ≤ W) (_ : x ∈ U) (a : Γ(X, U)), ∀ z, φ z ∈ U → gs φ z U a = t z) :
    ∃ θ : Γ(X, W), ∀ z, φ z ∈ W → gs φ z W θ = t z := by sorry
