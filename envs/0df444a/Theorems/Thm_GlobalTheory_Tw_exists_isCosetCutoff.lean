-- Prove2me | Theorems.Thm_GlobalTheory_Tw_exists_isCosetCutoff
-- name    : GlobalTheory.Tw.exists_isCosetCutoff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:26:11.104055+00:00
-- url     : https://prove2.me/theorems/a1f727a4-83b7-4bb4-bf37-3b01f2668e95
-- title:
--   Tw: exists is Coset Cutoff
-- statement:
--   The Tw construction uses the exists is Coset Cutoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/QuotIntegrableIffCutoff.lean#L57-L70

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
omit [SecondCountableTopology G]

theorem GlobalTheory.Tw.exists_isCosetCutoff [LocallyCompactSpace G] [T2Space G] (hT : IsClosed (T : Set G)) [μT.IsHaarMeasure]
    [μT.IsInvInvariant] : ∃ β : G → NNReal, Continuous β ∧ IsCosetCutoff T μT β := by sorry
