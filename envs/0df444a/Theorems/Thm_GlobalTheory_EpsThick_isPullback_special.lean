-- Prove2me | Theorems.Thm_GlobalTheory_EpsThick_isPullback_special
-- name    : GlobalTheory.EpsThick.isPullback_special
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:58:15.529471+00:00
-- url     : https://prove2.me/theorems/073ecf3d-268e-4c79-b99a-f0ab95563d3b
-- title:
--   Eps Thick: is Pullback special
-- statement:
--   The Eps Thick construction uses the is Pullback special property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstThickeningComplexFunctionsStructure.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ConstThickeningComplexFunctionsStructure.lean#L139-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
variable {R : Type} [CommRing R] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {π : Y' ⟶ Sp (DualNumber R)} {ρ : Y' ⟶ Y}

theorem GlobalTheory.EpsThick.isPullback_special (H : IsPullback ρ π q (spMap (algebraMap R (DualNumber R)))) {j : Y ⟶ Y'}
    (h₁ : j ≫ ρ = 𝟙 Y) (h₂ : j ≫ π = q ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom) :
    IsPullback j q π (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by sorry
