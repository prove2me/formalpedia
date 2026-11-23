-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_CofinalDual_measure_eq_relIndex_mul
-- name    : GlobalTheory.CompanionTheory.SW.CofinalDual.measure_eq_relIndex_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:16.274209+00:00
-- url     : https://prove2.me/theorems/6d08ed34-df30-4d09-842d-34c9c3695fd2
-- title:
--   Cofinal Dual: measure eq rel Index mul
-- statement:
--   The Cofinal Dual construction uses the measure eq rel Index mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L95-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AnnihilatorOfAnnihilatorLe.lean#L95-L136

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AnnihilatorOfAnnihilatorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CofinalDual

theorem GlobalTheory.CompanionTheory.SW.CofinalDual.measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddLeftInvariant] (S T : AddSubgroup V) (hST : S ≤ T) (hS : IsOpen (S : Set V))
    (hf : S.relIndex T ≠ 0) : μ T = S.relIndex T * μ S := by sorry
