-- Prove2me | Theorems.Thm_GlobalTheory_DegKer_card_fibre_eq
-- name    : GlobalTheory.DegKer.card_fibre_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:16.362493+00:00
-- url     : https://prove2.me/theorems/46a831b6-a5d0-482e-a971-022f958125b4
-- title:
--   Deg Ker: card fibre eq
-- statement:
--   The Deg Ker construction uses the card fibre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L61-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/MapDegreeEqExpCharPowMulCardKernel.lean#L61-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_SectionsHaveFiniteDimension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MapDegreeEqExpCharPowMulCardKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
noncomputable section
open GlobalTheory
open GlobalTheory.DegKer

theorem GlobalTheory.DegKer.card_fibre_eq {X Y : Scheme.{0}} (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens}
    (hU : IsAffineOpen U) (Ω : Type) [CommRing Ω] [Algebra Γ(Y, U) Ω] :
    letI := (f.app U).hom.toAlgebra
    Nat.card (Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] Ω) = Nat.card {y : Spec (CommRingCat.of Ω) ⟶ X //
      y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, U) Ω)) ≫ hU.fromSpec} := by sorry
