-- Prove2me | Theorems.Thm_GlobalTheory_Tw_IsQuotMeasure_eq_map
-- name    : GlobalTheory.Tw.IsQuotMeasure.eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:12.252052+00:00
-- url     : https://prove2.me/theorems/2c027a42-67d3-46fb-b126-1382e4a0e894
-- title:
--   Is Quot Measure: eq map
-- statement:
--   The Is Quot Measure construction uses the eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L107-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L107-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G]

theorem GlobalTheory.Tw.IsQuotMeasure.eq_map {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) {β : G → NNReal}
    (hβ : IsCosetCutoff T μT β) :
    ν = (μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T)) := by sorry
