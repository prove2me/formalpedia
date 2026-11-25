-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isClosed
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isClosed
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:52.610878+00:00
-- url     : https://prove2.me/theorems/4de48419-9f20-4bec-8bff-147aa7b8b87d
-- title:
--   Is Exp Lie Algebra: is Closed
-- statement:
--   The Is Exp Lie Algebra construction uses the is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L111-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L111-L144

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isClosed (h : IsExpLieAlgebra G 𝔤) : IsClosed (G : Set 𝔸ˣ) := by sorry
