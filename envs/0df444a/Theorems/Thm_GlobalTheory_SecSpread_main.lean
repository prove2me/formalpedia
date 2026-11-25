-- Prove2me | Theorems.Thm_GlobalTheory_SecSpread_main
-- name    : GlobalTheory.SecSpread.main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:09:48.983233+00:00
-- url     : https://prove2.me/theorems/a969a222-b924-5d9a-bed4-4ced155ef88e
-- title:
--   Sec Spread: main
-- statement:
--   The Sec Spread construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L180-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsDenomOfIsAffineOpen.lean#L180-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsDenomOfIsAffineOpen
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main

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

theorem GlobalTheory.SecSpread.main : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left), L.IsLB → ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (G' : Scheme.{0}) (φ : G' ⟶ G.left) (π : G' ⟶ Sp K), IsPullback φ π G.hom (spMap (algebraMap R K)) → (∃ (s : (L.pull φ).Sec) (j : (L.pull φ).ι), s.f j ≠ 0) → ∃ h : R, h ≠ 0 ∧ ∃ θ ∈ secOn L (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen h), ∀ y : Sp R, y ∈ PrimeSpectrum.basicOpen h → ∃ (g : G.left) (i : L.ι), G.hom g = y ∧ g ∈ G.left.basicOpen (θ i) := by sorry
