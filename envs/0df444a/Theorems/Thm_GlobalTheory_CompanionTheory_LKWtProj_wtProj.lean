-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LKWtProj_wtProj
-- name    : GlobalTheory.CompanionTheory.LKWtProj.wtProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:11.593848+00:00
-- url     : https://prove2.me/theorems/a41344a7-29bc-4977-ba1b-3c2b5de129c6
-- title:
--   LKWt Proj: wt Proj
-- statement:
--   The LKWt Proj construction uses the wt Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L99-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/LowKTypeMultiplicity/EigenspaceCyclicDensity/CreationOperators/WtProj.lean#L99-L130

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_CreationOperators_WtProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LKWtProj
open CompanionTheory.D.LK
open CompanionTheory.D.DSIC (KRel KUnit KStab)

theorem GlobalTheory.CompanionTheory.LKWtProj.wtProj : CompanionTheory.D.LK.WtProj := by sorry
