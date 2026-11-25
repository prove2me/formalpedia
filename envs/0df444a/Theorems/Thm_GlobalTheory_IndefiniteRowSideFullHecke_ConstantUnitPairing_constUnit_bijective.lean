-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConstantUnitPairing_constUnit_bijective
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing.constUnit_bijective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:08:32.456258+00:00
-- url     : https://prove2.me/theorems/db937fa5-6a20-47cd-9421-d03aa8b5649b
-- title:
--   Constant Unit Pairing: const Unit bijective
-- statement:
--   The Constant Unit Pairing construction uses the const Unit bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/ConstantUnitPairing.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/ConstantUnitPairing.lean#L28-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_ConstantUnitPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem GlobalTheory.IndefiniteRowSideFullHecke.ConstantUnitPairing.constUnit_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] : Function.Bijective (constUnit R F) := by sorry
