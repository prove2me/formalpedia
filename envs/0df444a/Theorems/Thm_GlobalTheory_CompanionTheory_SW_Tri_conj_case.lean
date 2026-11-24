-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Tri_conj_case
-- name    : GlobalTheory.CompanionTheory.SW.Tri.conj_case
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:32.698645+00:00
-- url     : https://prove2.me/theorems/be9f61b8-1724-44ed-baeb-8d565ab082f3
-- title:
--   Tri: conj case
-- statement:
--   The Tri construction uses the conj case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L255-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HermitianOrbitLocalSectionSubgroup.lean#L255-L300

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

theorem GlobalTheory.CompanionTheory.SW.Tri.conj_case (sig : K →+* K) (Hm : AddSubgroup (Matrix (Fin n) (Fin n) K))
    (hH : ∀ S ∈ Hm, ∀ g : Matrix (Fin n) (Fin n) K, cT sig g * S * g ∈ Hm)
    (G : GL (Fin n) K) (Q₀ : Subgroup (GL (Fin n) K)) (o₀ : Q₀ → Hm) (ho₀ : IsOpenEmbedding o₀)
    (D : Matrix (Fin n) (Fin n) K)
    (hf : ∀ x : Q₀, (o₀ x : Matrix (Fin n) (Fin n) K) =
      cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * D * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ (Q : Subgroup (GL (Fin n) K)) (_ : Q ≃ₜ Q₀) (o : Q → Hm), IsOpenEmbedding o ∧
      ∀ x : Q, (o x : Matrix (Fin n) (Fin n) K) =
        cT sig ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (cT sig (G : Matrix (Fin n) (Fin n) K) * D * (G : Matrix (Fin n) (Fin n) K)) *
          ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by sorry
