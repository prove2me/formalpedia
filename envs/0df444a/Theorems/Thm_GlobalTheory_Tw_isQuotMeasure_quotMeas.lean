-- Prove2me | Theorems.Thm_GlobalTheory_Tw_isQuotMeasure_quotMeas
-- name    : GlobalTheory.Tw.isQuotMeasure_quotMeas
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:55.918208+00:00
-- url     : https://prove2.me/theorems/9ab92d53-61dd-461e-9f53-3fe13e1aa129
-- title:
--   Tw: is Quot Measure quot Meas
-- statement:
--   The Tw construction uses the is Quot Measure quot Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L126-L130

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

theorem GlobalTheory.Tw.isQuotMeasure_quotMeas (hT : IsClosed (T : Set G)) : IsQuotMeasure T μ μT (quotMeas T μ μT) := by sorry
