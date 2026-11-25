-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompact_unitaryGroup_entries
-- name    : GroundTheory.Automorphic.isCompact_unitaryGroup_entries
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:08:14.857378+00:00
-- url     : https://prove2.me/theorems/77ce1f1a-6c55-4278-a0d6-57f9b6d27966
-- title:
--   Automorphic: is Compact unitary Group entries
-- statement:
--   The Automorphic construction uses the is Compact unitary Group entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L155-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L155-L165

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

theorem GroundTheory.Automorphic.isCompact_unitaryGroup_entries : IsCompact (Matrix.unitaryGroup ι 𝕜 : Set (Matrix ι ι 𝕜)) := by sorry
