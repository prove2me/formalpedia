-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IndicatorFunctionIdentity_isOpen_lat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:48.855648+00:00
-- url     : https://prove2.me/theorems/4bb485ae-9f8c-47b4-aa46-5be29858bde6
-- title:
--   Indicator Function Identity: is Open lat
-- statement:
--   The Indicator Function Identity construction uses the is Open lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IndicatorFunctionIdentity.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IndicatorFunctionIdentity.lean#L22-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.SplitWeil GlobalTheory.LatPair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsOpen (L : Set (n → k)) := by sorry
