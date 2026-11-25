-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_analyticAt_expChartProd
-- name    : GroundTheory.Automorphic.analyticAt_expChartProd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:41.704358+00:00
-- url     : https://prove2.me/theorems/9b437c59-71be-47ec-8549-46b3f3cab646
-- title:
--   Automorphic: analytic At exp Chart Prod
-- statement:
--   The Automorphic construction uses the analytic At exp Chart Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L56-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L56-L65

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

theorem GroundTheory.Automorphic.analyticAt_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    (p : EuclideanSpace ℝ (Fin d) × ℝ) : AnalyticAt ℝ (expChartProd b X) p := by sorry
