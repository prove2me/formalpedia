-- Prove2me | Theorems.Thm_GlobalTheory_T_scaledIntegersK_annihilator_small_near_zero
-- name    : GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:56:15.704644+00:00
-- url     : https://prove2.me/theorems/544051c4-6c04-47fb-9a40-cd374f79f2cc
-- title:
--   T: scaled Integers K annihilator small near zero
-- statement:
--   The T construction uses the scaled Integers K annihilator small near zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ScaledIntegersKAnnihilatorSmallNearZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ScaledIntegersKAnnihilatorSmallNearZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ScaledIntegersKAnnihilatorSmallNearZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ U ∈ 𝓝 (0 : A.K), ∀ᶠ c in 𝓝[≠] (0 : F), ∀ b : A.K, (∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1) → b ∈ U := by sorry
