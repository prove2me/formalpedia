-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_exists_homeo
-- name    : GlobalTheory.CompanionTheory.SW.HermTop.exists_homeo
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:20.484831+00:00
-- url     : https://prove2.me/theorems/6316b3a1-db54-4433-a012-2050054ed2e4
-- title:
--   Herm Top: exists homeo
-- statement:
--   The Herm Top construction uses the exists homeo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianMatricesLocallyCompactBorel.lean#L46-L53

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.SW.HermTop.exists_homeo [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by sorry
