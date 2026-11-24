-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BB_coordK_eq_map
-- name    : GlobalTheory.CompanionTheory.SW.BB.coordK_eq_map
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:02:57.063286+00:00
-- url     : https://prove2.me/theorems/70984639-1b0a-4a2b-bbca-023a3a4a1f21
-- title:
--   BB: coord K eq map
-- statement:
--   The BB construction uses the coord K eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHomeomorphRankOneTuples.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CoordinateHomeomorphRankOneTuples.lean#L30-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.BB.coordK_eq_map {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (e : R ⊗[F] E ≃ᵐ (Fin d → R))
    (he : ∀ y k, e y k = (Algebra.TensorProduct.basis R b).repr y k) :
    coordK R b lam = (Measure.pi fun _ => lam).map e.symm := by sorry
