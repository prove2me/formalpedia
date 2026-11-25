-- Prove2me | Theorems.Thm_GlobalTheory_NormGlue_valF_comp_appIso
-- name    : GlobalTheory.NormGlue.valF_comp_appIso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:27:15.253796+00:00
-- url     : https://prove2.me/theorems/ce3e1c02-817d-594c-a442-8f278b85b566
-- title:
--   Norm Glue: val F comp app Iso
-- statement:
--   The Norm Glue construction uses the val F comp app Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L38-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L38-L52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue

theorem GlobalTheory.NormGlue.valF_comp_appIso {F : Type} [Field F] {X Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (V : Y.Opens) (u : Γ(Y, V)) (y₀ : Sp F ⟶ Y) :
    valF (y₀ ≫ f) (f ''ᵁ V) ((f.appIso V).inv.hom u) = valF y₀ V u := by sorry
