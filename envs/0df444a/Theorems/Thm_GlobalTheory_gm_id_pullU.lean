-- Prove2me | Theorems.Thm_GlobalTheory_gm_id_pullU
-- name    : GlobalTheory.gm_id_pullU
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:23.053386+00:00
-- url     : https://prove2.me/theorems/be4cc5f9-68f7-5f8e-b372-ae9c12741b63
-- title:
--   Global Theory: gm id pull U
-- statement:
--   The Global Theory construction uses the gm id pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/NonemptyIsLimitBaseChange.lean#L45-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {Y : Scheme.{0}}

theorem GlobalTheory.gm_id_pullU {X : Scheme.{0}} (F : Y ⟶ X) (y : Y) (U : X.Opens) (hy : F y ∈ U) (t : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (F ⁻¹ᵁ U) (pullU F U t) = gm F y U t := by sorry
