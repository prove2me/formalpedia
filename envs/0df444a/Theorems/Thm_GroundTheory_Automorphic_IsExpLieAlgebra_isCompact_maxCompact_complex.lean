-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isCompact_maxCompact_complex
-- name    : GroundTheory.Automorphic.IsExpLieAlgebra.isCompact_maxCompact_complex
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:29.551827+00:00
-- url     : https://prove2.me/theorems/61069c7f-3b89-59b6-b525-bf0ca7f8eed7
-- title:
--   Is Exp Lie Algebra: is Compact max Compact complex
-- statement:
--   The Is Exp Lie Algebra construction uses the is Compact max Compact complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L202-L205

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
open Matrix
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GroundTheory.Automorphic.IsExpLieAlgebra.isCompact_maxCompact_complex {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) := by sorry
