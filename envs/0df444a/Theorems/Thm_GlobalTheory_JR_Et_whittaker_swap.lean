-- Prove2me | Theorems.Thm_GlobalTheory_JR_Et_whittaker_swap
-- name    : GlobalTheory.JR.Et.whittaker_swap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:22:53.452796+00:00
-- url     : https://prove2.me/theorems/474dd78b-cc77-4ab4-a314-5948b9c32017
-- title:
--   Et: whittaker swap
-- statement:
--   The Et construction uses the whittaker swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerSwap.lean#L41-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerSwap.lean#L41-L112

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerSwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Et

theorem GlobalTheory.JR.Et.whittaker_swap : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (μ : Measure A.L), μ.IsAddHaarMeasure → ∀ φ : A.L → ℂ, IsTest φ → ∀ (x a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ) * A.psiK ψ (-(a * z)) ∂μK = ∫ y, φ y * ∫ z in {z : A.K | c • z ∈ A.OK}, A.psiK ψ (z * (x * A.NL y - a)) ∂μK ∂μ := by sorry
