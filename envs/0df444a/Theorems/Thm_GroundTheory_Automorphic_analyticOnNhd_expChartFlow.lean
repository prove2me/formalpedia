-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_analyticOnNhd_expChartFlow
-- name    : GroundTheory.Automorphic.analyticOnNhd_expChartFlow
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:35.080588+00:00
-- url     : https://prove2.me/theorems/2ac9fa7e-8316-4117-9b92-ea9652316b6c
-- title:
--   Automorphic: analytic On Nhd exp Chart Flow
-- statement:
--   The Automorphic construction uses the analytic On Nhd exp Chart Flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L79-L81

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped ContDiff
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GroundTheory.Automorphic.analyticOnNhd_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    AnalyticOnNhd ℝ (expChartFlow b X) (expChartProd b X ⁻¹' (expPartialHomeomorph ℝ 𝔸).target) := by sorry
