-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_isAbelianScheme_field
-- name    : GlobalTheory.isIntegral_of_isAbelianScheme_field
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:17.635577+00:00
-- url     : https://prove2.me/theorems/aab83b60-b4e1-47b3-ac5e-a41d92f7c027
-- title:
--   Global Theory: is Integral of is Abelian Scheme field
-- statement:
--   The Global Theory construction uses the is Integral of is Abelian Scheme field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsIntegralOfIsAbelianSchemeField.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsIntegralOfIsAbelianSchemeField.lean#L12-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.isIntegral_of_isAbelianScheme_field (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) : IsIntegral A.left := by sorry
