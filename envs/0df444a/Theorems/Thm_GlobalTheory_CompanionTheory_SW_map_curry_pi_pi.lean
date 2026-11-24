-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_map_curry_pi_pi
-- name    : GlobalTheory.CompanionTheory.SW.map_curry_pi_pi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:17.509906+00:00
-- url     : https://prove2.me/theorems/0a427bc6-de3f-483e-957b-20b7dd1b52b4
-- title:
--   SW: map curry pi pi
-- statement:
--   The SW construction uses the map curry pi pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasurableCoordinateMapsTensor.lean#L11-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MeasurableCoordinateMapsTensor.lean#L11-L26

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasurableCoordinateMapsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.map_curry_pi_pi {R : Type} [MeasurableSpace R] (lam : Measure R) [SigmaFinite lam] (M d : ℕ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin d => lam).map
      (fun (Y : Fin M → Fin d → R) (p : Fin M × Fin d) => Y p.1 p.2) =
      Measure.pi fun _ : Fin M × Fin d => lam := by sorry
