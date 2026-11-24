-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_continuous_map
-- name    : GlobalTheory.CompanionTheory.SW.Glue.continuous_map
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:25.499192+00:00
-- url     : https://prove2.me/theorems/40980849-de20-48a9-9fc7-3ed5bc3eec93
-- title:
--   Glue: continuous map
-- statement:
--   The Glue construction uses the continuous map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L39-L51

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.SW.Glue.continuous_map {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Continuous fun y : R ⊗[F] E => Algebra.TensorProduct.map φ (AlgHom.id F E) y := by sorry
