-- Prove2me | Theorems.Thm_GlobalTheory_MaxLatStruct_colon_eq_prod
-- name    : GlobalTheory.MaxLatStruct.colon_eq_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:39.452828+00:00
-- url     : https://prove2.me/theorems/0c869bb5-63ec-55bd-88f1-d564cdf6cb26
-- title:
--   Max Lat Struct: colon eq prod
-- statement:
--   The Max Lat Struct construction uses the colon eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L347-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MaximalHermitianLatticeLocalStructureDiscriminan.lean#L347-L365

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

theorem GlobalTheory.MaxLatStruct.colon_eq_prod (hσ : ∀ r, algebraMap R K (σ r) = star (algebraMap R K r)) (hs : h.IsSymm)
    (hM : IsMaxLat h M) (hJ : M.colon (dual h M : Set V) ≠ ⊥) (T : Finset (Ideal R))
    (hT : ∀ P, P ∈ T ↔ P.IsMaximal ∧ M.colon (dual h M : Set V) ≤ P) :
    M.colon (dual h M : Set V) = ∏ P ∈ T, P := by sorry
