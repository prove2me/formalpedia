-- Prove2me | Theorems.Thm_GlobalTheory_IwasawaShape_finiteOnCompacts_of_nhds
-- name    : GlobalTheory.IwasawaShape.finiteOnCompacts_of_nhds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:22:36.009119+00:00
-- url     : https://prove2.me/theorems/689b985f-fa19-4307-a795-336e3ba0af98
-- title:
--   Iwasawa Shape: finite On Compacts of nhds
-- statement:
--   The Iwasawa Shape construction uses the finite On Compacts of nhds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLintegralEqOfMeasurable.lean#L245-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsLintegralEqOfMeasurable.lean#L245-L255

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMapMulRightEqSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsLintegralEqOfMeasurable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.IwasawaShape
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem GlobalTheory.IwasawaShape.finiteOnCompacts_of_nhds (S : Subgroup G) (ν : Measure G) (h : ν (S : Set G)ᶜ = 0)
    (hS : IsClosed (S : Set G)) (hi : ∀ s ∈ S, ν.map (fun g => s * g) = ν) (B : Set G) (hBm : MeasurableSet B)
    (hB : B ∈ nhds (1 : G)) (hf : ν B ≠ ⊤) : IsFiniteMeasureOnCompacts ν := by sorry
