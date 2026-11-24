-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_exists_stableGauss
-- name    : GlobalTheory.JR.WeilQuad.exists_stableGauss
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:33.034983+00:00
-- url     : https://prove2.me/theorems/6420490d-6585-4a8c-b97a-301689357824
-- title:
--   Weil Quad: exists stable Gauss
-- statement:
--   The Weil Quad construction uses the exists stable Gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsStableQuadraticGaussIntegral.lean#L66-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsStableQuadraticGaussIntegral.lean#L66-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilUnipotentTorusPreserveTest
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsStableQuadraticGaussIntegral
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
open GlobalTheory.JR.WeilQuad.GaussStable

theorem GlobalTheory.JR.WeilQuad.exists_stableGauss : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L)
    (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ u : A.Kˣ, ∃ G, IsStableGauss A ψ x μ u G := by sorry
