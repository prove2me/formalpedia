-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_InfPush_map_coord_pi
-- name    : GlobalTheory.CompanionTheory.SW.BB.InfPush.map_coord_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:42.945863+00:00
-- url     : https://prove2.me/theorems/4b0fa73e-4aa4-46b2-8770-0339843ce551
-- title:
--   Inf Push: map coord pi
-- statement:
--   The Inf Push construction uses the map coord pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanCoordinateMeasureTransport.lean#L79-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanCoordinateMeasureTransport.lean#L79-L98

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

theorem GlobalTheory.CompanionTheory.SW.BB.InfPush.map_coord_pi {ι κ A : Type} [Fintype ι] [Fintype κ] [MeasurableSpace A]
    (lam : Measure A) [SigmaFinite lam] (e : A → κ → ℝ) (he : Measurable e) (c : ℝ≥0)
    (hlam : lam.map e = (c : ℝ≥0∞) • (volume : Measure (κ → ℝ))) :
    (Measure.pi fun _ : ι => lam).map (fun y w p => e (y p) w) =
      ((c : ℝ≥0∞) ^ Fintype.card ι) • (volume : Measure (κ → ι → ℝ)) := by sorry
