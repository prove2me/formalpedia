-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_good_at
-- name    : GlobalTheory.CompanionTheory.SW.GoodRing.good_at
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:04:04.44436+00:00
-- url     : https://prove2.me/theorems/0590e294-4852-46c0-863a-8c0731667faf
-- title:
--   Good Ring: good at
-- statement:
--   The Good Ring construction uses the good at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L285-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorIntegerRingAlmostAllPlaces.lean#L285-L401

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodRing
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.GoodRing.good_at (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (b₂ : Module.Basis (Fin 2) F E) (D : F) (hb0 : b₂ 0 = 1) (hσ1 : σ (b₂ 1) = -b₂ 1)
    (hD : b₂ 1 * b₂ 1 = algebraMap F E D) (v : HeightOneSpectrum (𝓞 F))
    (hD1 : Valued.v (algebraMap F (Fv F v) D) = 1)
    (h21 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (h31 : Valued.v (algebraMap F (Fv F v) 3) = 1)
    (hBC : ∀ k j, (Algebra.TensorProduct.basis (Fv F v) b₂).repr (inclR (Fv F v) (b k)) j ∈
      v.adicCompletionIntegers F)
    (hCB : ∀ j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) (b₂ j)) k ∈
      v.adicCompletionIntegers F) :
    ∃ O : Subring (Fv F v ⊗[F] E),
      (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F) ∧
      (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧
      (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧
      (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O,
        (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧
        ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧
      ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β →
        ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by sorry
