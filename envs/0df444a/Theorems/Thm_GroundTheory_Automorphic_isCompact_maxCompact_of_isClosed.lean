-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompact_maxCompact_of_isClosed
-- name    : GroundTheory.Automorphic.isCompact_maxCompact_of_isClosed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:15.510661+00:00
-- url     : https://prove2.me/theorems/394647fe-77c1-48d5-b00e-d353e6e3a1ce
-- title:
--   Automorphic: is Compact max Compact of is Closed
-- statement:
--   The Automorphic construction uses the is Compact max Compact of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L167-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L167-L195

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

theorem GroundTheory.Automorphic.isCompact_maxCompact_of_isClosed {G : Subgroup (Matrix ι ι 𝕜)ˣ}
    (hG : IsClosed (G : Set (Matrix ι ι 𝕜)ˣ)) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) := by sorry
