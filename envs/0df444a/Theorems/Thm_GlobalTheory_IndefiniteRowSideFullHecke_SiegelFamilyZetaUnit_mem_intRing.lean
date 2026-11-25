-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_SiegelFamilyZetaUnit_mem_intRing
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.mem_intRing
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:20.40828+00:00
-- url     : https://prove2.me/theorems/dccae57b-0fe1-48ac-9c78-e15faed821bf
-- title:
--   Siegel Family Zeta Unit: mem int Ring
-- statement:
--   The Siegel Family Zeta Unit construction uses the mem int Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SiegelFamilyZetaUnit.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SiegelFamilyZetaUnit.lean#L27-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SiegelFamilyZetaUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit.mem_intRing {C : Type} [NormedField C] [IsUltrametricDist C] (x : C) : x ∈ intRing C ↔ ‖x‖ ≤ 1 := by sorry
