-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NonNorm_level0
-- name    : GlobalTheory.JR.WeilQuad.NonNorm.level0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:07:05.498125+00:00
-- url     : https://prove2.me/theorems/d1526f37-a5ff-5607-bb2c-50f1f651c05d
-- title:
--   Non Norm: level0
-- statement:
--   The Non Norm construction uses the level0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaussAtUniformiser.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaussAtUniformiser.lean#L86-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableQuadraticGaussIntegralMulNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticExistsIntegersUniformiserStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianTraceDualIntegersEqUniformizerPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HaarMeasureLUnitSmulAbsKSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticGaussIntegralStableOfDualLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormFormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaussAtUniformiser
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NonNorm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.NonNorm.level0 : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ O : Subring A.L, IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) → ∀ t : A.K, {y : A.L | ∀ m ∈ O, A.kerL ψ (t * x) y m = 1} = (O : Set A.L) → IsStableGauss A ψ x μ t (((μ (O : Set A.L)).toReal : ℝ) : ℂ) := by sorry
