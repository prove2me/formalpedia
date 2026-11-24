-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_continuous_expChartProd
-- name    : GroundTheory.Automorphic.continuous_expChartProd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:13.721165+00:00
-- url     : https://prove2.me/theorems/31108559-55ee-475e-b81c-4973fef1e124
-- title:
--   Automorphic: continuous exp Chart Prod
-- statement:
--   The Automorphic construction uses the continuous exp Chart Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L48-L54

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

theorem GroundTheory.Automorphic.continuous_expChartProd {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤) :
    Continuous (expChartProd b X) := by sorry
