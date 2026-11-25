-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AdelicDegreeTameRamification_LFunction_one_ne_zero
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.LFunction_one_ne_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:36:08.667418+00:00
-- url     : https://prove2.me/theorems/0a7a6624-184a-484c-b76e-52f512d87d08
-- title:
--   Adelic Degree Tame Ramification: LFunction one ne zero
-- statement:
--   The Adelic Degree Tame Ramification construction uses the LFunction one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/AdelicDegreeTameRamification.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/AdelicDegreeTameRamification.lean#L116-L117

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.LFunction_one_ne_zero (H : Host E) : (quadChar H).LFunction 1 ≠ 0 := by sorry
