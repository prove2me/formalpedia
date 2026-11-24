-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_aMat_gram
-- name    : GlobalTheory.CompanionTheory.SW.Tri.aMat_gram
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:53.565634+00:00
-- url     : https://prove2.me/theorems/86a8acf7-fbcd-4132-9fbe-ce0ea5efccf8
-- title:
--   Tri: a Mat gram
-- statement:
--   The Tri construction uses the a Mat gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L170-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L170-L188

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

theorem GlobalTheory.CompanionTheory.SW.Tri.aMat_gram (ι : R →+* K) (sig : K →+* K) (hs : ∀ r, sig (ι r) = ι r) {U : Subgroup Rˣ}
    (u : Fin n → U) (m : {p : Fin n × Fin n // p.1 < p.2} → K) (d : Fin n → Rˣ) :
    cT sig (aMat ι u m) * Matrix.diagonal (fun i => ι (d i : R)) * aMat ι u m
      = cT sig (nMat m) * Matrix.diagonal (fun i => ι ((((u i : Rˣ) ^ 2 * d i : Rˣ)) : R)) * nMat m := by sorry
