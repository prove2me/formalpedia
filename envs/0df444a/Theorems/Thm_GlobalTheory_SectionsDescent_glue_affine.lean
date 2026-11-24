-- Prove2me | Theorems.Thm_GlobalTheory_SectionsDescent_glue_affine
-- name    : GlobalTheory.SectionsDescent.glue_affine
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:51:44.525796+00:00
-- url     : https://prove2.me/theorems/599b984a-3da8-4a44-b871-adaab5577d9e
-- title:
--   Sections Descent: glue affine
-- statement:
--   The Sections Descent construction uses the glue affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L61-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L61-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
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
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange

theorem GlobalTheory.SectionsDescent.glue_affine {X : Scheme.{0}} (U : X.Opens)
    (f : ∀ (V : X.Opens), IsAffineOpen V → V ≤ U → Γ(X, V))
    (hf : ∀ V W hV hW (hVU : V ≤ U) (h : W ≤ V), rs h (f V hV hVU) = f W hW (h.trans hVU)) :
    ∃ y : Γ(X, U), ∀ V hV (h : V ≤ U), rs h y = f V hV h := by sorry
