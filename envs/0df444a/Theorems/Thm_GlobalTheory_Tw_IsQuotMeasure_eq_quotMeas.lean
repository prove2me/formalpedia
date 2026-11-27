-- Prove2me | Theorems.Thm_GlobalTheory_Tw_IsQuotMeasure_eq_quotMeas
-- name    : GlobalTheory.Tw.IsQuotMeasure.eq_quotMeas
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:02.176263+00:00
-- url     : https://prove2.me/theorems/eeb3dc60-864c-5fd7-8839-f6a0a94b8eae
-- title:
--   Is Quot Measure: eq quot Meas
-- statement:
--   The Is Quot Measure construction uses the eq quot Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L132-L135

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
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]

theorem GlobalTheory.Tw.IsQuotMeasure.eq_quotMeas (hT : IsClosed (T : Set G)) {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) :
    ν = quotMeas T μ μT := by sorry
