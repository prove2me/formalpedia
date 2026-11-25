-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HalfPowerSpherical_isChain_chainGen
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical.isChain_chainGen
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:44.318559+00:00
-- url     : https://prove2.me/theorems/777120fe-6886-5b38-b188-11a9ad11f9c4
-- title:
--   Half Power Spherical: is Chain chain Gen
-- statement:
--   The Half Power Spherical construction uses the is Chain chain Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HalfPowerSpherical.lean#L278-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HalfPowerSpherical.lean#L278-L291

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical.isChain_chainGen (α α' : kˣ) (m : ℕ) : IsChain α α' m (chainGen α α' m) := by sorry
