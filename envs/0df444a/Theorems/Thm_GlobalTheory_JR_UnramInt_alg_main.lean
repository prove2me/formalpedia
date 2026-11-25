-- Prove2me | Theorems.Thm_GlobalTheory_JR_UnramInt_alg_main
-- name    : GlobalTheory.JR.UnramInt.alg_main
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:44:20.636488+00:00
-- url     : https://prove2.me/theorems/2ae33613-5175-4960-98a1-f53c2e9a5b67
-- title:
--   Unram Int: alg main
-- statement:
--   The Unram Int construction uses the alg main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticExistsIntegersUniformiser.lean#L17-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticExistsIntegersUniformiser.lean#L17-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormGroupSignMulAndNegOne
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNormSurj
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RamificationIndexEqOneOfAdjoinRangeEqTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticUniformizerTraceNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiser
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.UnramInt
open ValuativeRel GroundTheory.LocalField

theorem GlobalTheory.JR.UnramInt.alg_main : ∀ (F E K L : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [LocallyCompactSpace F] [NontriviallyNormedField E] [NormedAlgebra F E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L],
    (∀ y : E, ∃ x : F, ‖y‖ = ‖x‖) → Module.finrank K L = 2 →
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    ∃ (ϖ : Kˣ) (O : Subring L), (O : Set L) = {y | spectralNorm F L y ≤ 1} ∧
      (¬ ∃ y : L, Algebra.norm K y = (ϖ : K)) ∧ algebraMap K L (ϖ : K) ∈ O ∧
      (¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1) ∧
      (∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧
      (∀ s : K, algebraMap K L s ∈ O → ∃ z ∈ O, Algebra.trace K L z = s) ∧
      (∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, Algebra.norm K w = s) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ z ∈ O, spectralNorm F L (algebraMap K L ((ϖ : K) ^ n) * z) < r) ∧
      ∀ y : L, ∃ n : ℕ, algebraMap K L ((ϖ : K) ^ n) * y ∈ O := by sorry
