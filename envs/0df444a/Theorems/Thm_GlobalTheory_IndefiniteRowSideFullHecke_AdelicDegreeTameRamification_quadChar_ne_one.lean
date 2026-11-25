-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdelicDegreeTameRamification_quadChar_ne_one
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadChar_ne_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:37:11.366448+00:00
-- url     : https://prove2.me/theorems/12a446e3-f269-57f8-9d61-8ace631d2048
-- title:
--   Adelic Degree Tame Ramification: quad Char ne one
-- statement:
--   The Adelic Degree Tame Ramification construction uses the quad Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/AdelicDegreeTameRamification.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/AdelicDegreeTameRamification.lean#L108-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_AdelicDegreeTameRamification
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadChar_ne_one (H : Host E) : quadChar H ≠ 1 := by sorry
