-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_sq_open
-- name    : GlobalTheory.CompanionTheory.SW.Tri.sq_open
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:39.826698+00:00
-- url     : https://prove2.me/theorems/b1e68edb-2cfb-42c0-9a37-cf20b52d4e39
-- title:
--   Tri: sq open
-- statement:
--   The Tri construction uses the sq open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L248-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L248-L253

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOpenChartDiagonalUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHermitianDiagonalizationUnitsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentitiesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOrbitLocalSectionSubgroup
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Tri
variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
variable [TopologicalSpace R] [TopologicalSpace K] [IsTopologicalRing R] [IsTopologicalRing K]

theorem GlobalTheory.CompanionTheory.SW.Tri.sq_open (U : Subgroup Rˣ) (hU : IsOpenEmbedding (fun u : U => ((u : Rˣ) ^ 2 : Rˣ)))
    (d : Fin n → Rˣ) :
    IsOpenEmbedding (fun p : (Fin n → U) × ({p : Fin n × Fin n // p.1 < p.2} → K) =>
      ((fun i => (p.1 i : Rˣ) ^ 2 * d i : Fin n → Rˣ), p.2)) := by sorry
