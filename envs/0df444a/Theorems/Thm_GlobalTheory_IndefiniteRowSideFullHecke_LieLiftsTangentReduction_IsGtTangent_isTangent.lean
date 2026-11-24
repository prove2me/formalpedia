-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LieLiftsTangentReduction_IsGtTangent_isTangent
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction.IsGtTangent.isTangent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:08:37.093013+00:00
-- url     : https://prove2.me/theorems/464869f8-2d9c-4ec5-a978-ba9f9bf89762
-- title:
--   Is Gt Tangent: is Tangent
-- statement:
--   The Is Gt Tangent construction uses the is Tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LieLiftsTangentReduction.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/HeightDefect/LieLiftsTangentReduction.lean#L18-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_LieLiftsTangentReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj

theorem GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction.IsGtTangent.isTangent {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ν : GtPt D (epsR R)}
    (h : IsGtTangent ν) : IsTangent ν.b := by sorry
