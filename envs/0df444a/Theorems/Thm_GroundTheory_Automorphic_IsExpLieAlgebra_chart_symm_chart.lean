-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_chart_symm_chart
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.chart_symm_chart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:53.634223+00:00
-- url     : https://prove2.me/theorems/e35fbde5-6952-4bcf-bff8-f534c33a50d0
-- title:
--   Is Exp Lie Algebra: chart symm chart
-- statement:
--   The Is Exp Lie Algebra construction uses the chart symm chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinSeries.lean#L101-L103

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_SmoothVectors
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)

theorem GroundTheory.Automorphic.IsExpLieAlgebra.chart_symm_chart {g x : G} (hx : x ∈ (h.chart g).source) :
    g * h.expG (h.chart g x) = x := by sorry
