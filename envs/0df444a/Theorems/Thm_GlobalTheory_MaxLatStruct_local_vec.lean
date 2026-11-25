-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_local_vec
-- name    : GlobalTheory.MaxLatStruct.local_vec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:01:02.357377+00:00
-- url     : https://prove2.me/theorems/3d87b8bb-9f22-4e9c-8d0e-42eb207db6b4
-- title:
--   Max Lat Struct: local vec
-- statement:
--   The Max Lat Struct construction uses the local vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L423-L471
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L423-L471

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatStruct
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule R V} {σ : R →+* R}

theorem GlobalTheory.MaxLatStruct.local_vec (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) {P : Ideal R} (hP : P.IsMaximal) (hin : ∀ r, σ r ∈ P ↔ r ∈ P)
    {π : R} (h1 : π ∈ P) (h2 : π ∉ P ^ 2) {y : V} (hy : y ∈ dual h M) (hPy : ∀ p ∈ P, p • y ∈ M) (hyM : y ∉ M)
    (hgen : ∀ z ∈ dual h M, ∃ s ∉ P, ∃ c : R, s • z - c • y ∈ M) :
    ∃ x ∈ M, (∃ a : R, algebraMap R K a = h x x ∧ a ∈ P ∧ a ∉ P ^ 2) ∧
      ∀ z ∈ loc (K := K) P (dual h M), ∃ c ∈ locR (K := K) P, z - (c * (h x x)⁻¹) • x ∈ loc (K := K) P M := by sorry
