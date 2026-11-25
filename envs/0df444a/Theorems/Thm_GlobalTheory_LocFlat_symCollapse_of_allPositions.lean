-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_symCollapse_of_allPositions
-- name    : GlobalTheory.LocFlat.symCollapse_of_allPositions
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:17.220822+00:00
-- url     : https://prove2.me/theorems/3b2d3e12-217e-5816-ab71-b7712d1ac364
-- title:
--   Loc Flat: sym Collapse of all Positions
-- statement:
--   The Loc Flat construction uses the sym Collapse of all Positions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymCollapseOfAllPositions.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymCollapseOfAllPositions.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainPatternIterated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnIndicatorPureAtSymmetricPositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowIndicatorOfSymLevelExchangeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPositionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymLevelDoubleStepOfFlatColumnFlatRowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymCollapseOfAllPositions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat

theorem GlobalTheory.LocFlat.symCollapse_of_allPositions : AllPositions → GlobalTheory.LocFlat.SymCollapse := by sorry
