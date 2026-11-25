-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Transp_genus_img
-- name    : GlobalTheory.Mass.Transp.genus_img
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T06:04:02.228687+00:00
-- url     : https://prove2.me/theorems/dcc644cd-a864-5b6e-9f31-af8a7cf047d0
-- title:
--   Transp: genus img
-- statement:
--   The Transp construction uses the genus img property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatsDiscStable.lean#L231-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LatsDiscStable.lean#L231-L240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumTransportEquivariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatsDiscStable
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Transp
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open NumberField Matrix
open scoped ENNReal Classical
variable {R K V V' V'' : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
  [AddCommGroup V''] [Module K V''] [Module R V''] [IsScalarTower R K V'']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem GlobalTheory.Mass.Transp.genus_img (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L M : Submodule R V)
    (hM : M ∈ _root_.Formalism.HermitianLatticesTheory.genus h L) : _root_.GlobalTheory.Mass.Transp.img e M ∈ _root_.Formalism.HermitianLatticesTheory.genus h' (_root_.GlobalTheory.Mass.Transp.img e L) := by sorry
