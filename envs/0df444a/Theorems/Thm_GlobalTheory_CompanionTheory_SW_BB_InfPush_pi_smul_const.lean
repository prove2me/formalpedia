-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_InfPush_pi_smul_const
-- name    : GlobalTheory.CompanionTheory.SW.BB.InfPush.pi_smul_const
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:43.529402+00:00
-- url     : https://prove2.me/theorems/126689a4-4586-4e19-a034-2e3fb34c0998
-- title:
--   Inf Push: pi smul const
-- statement:
--   The Inf Push construction uses the pi smul const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanCoordinateMeasureTransport.lean#L69-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanCoordinateMeasureTransport.lean#L69-L77

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.InfPush

theorem GlobalTheory.CompanionTheory.SW.BB.InfPush.pi_smul_const {ι α : Type} [Fintype ι] [MeasurableSpace α] (ν : Measure α) [SigmaFinite ν]
    (c : ℝ≥0) :
    Measure.pi (fun _ : ι => (c : ℝ≥0∞) • ν) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • Measure.pi fun _ : ι => ν := by sorry
