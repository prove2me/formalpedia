-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_expG_expChartFlow
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.expG_expChartFlow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:40.986805+00:00
-- url     : https://prove2.me/theorems/0e49643b-58e6-43b4-aa45-b418d463952c
-- title:
--   Is Exp Lie Algebra: exp G exp Chart Flow
-- statement:
--   The Is Exp Lie Algebra construction uses the exp G exp Chart Flow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpChart.lean#L103-L114

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
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.expG_expChartFlow {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) (X : 𝔤)
    {p : EuclideanSpace ℝ (Fin d) × ℝ} (hp : expChartProd b X p ∈ h.nhdOne) :
    h.expG (coordEquiv b (expChartFlow b X p)) = h.expG (coordEquiv b p.1) * h.expG (p.2 • X) := by sorry
