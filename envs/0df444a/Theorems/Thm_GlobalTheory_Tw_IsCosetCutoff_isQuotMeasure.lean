-- Prove2me | Theorems.Thm_GlobalTheory_Tw_IsCosetCutoff_isQuotMeasure
-- name    : GlobalTheory.Tw.IsCosetCutoff.isQuotMeasure
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:13:00.666889+00:00
-- url     : https://prove2.me/theorems/c931eade-18f5-4632-97ac-f25e93929b57
-- title:
--   Is Coset Cutoff: is Quot Measure
-- statement:
--   The Is Coset Cutoff construction uses the is Quot Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L72-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L72-L103

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

theorem GlobalTheory.Tw.IsCosetCutoff.isQuotMeasure [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsMulLeftInvariant]
    [μT.IsInvInvariant] {β : G → NNReal} (hβ : IsCosetCutoff T μT β) :
    IsQuotMeasure T μ μT ((μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T))) := by sorry
