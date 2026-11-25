-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conjCME_apply
-- name    : GroundTheory.Automorphic.conjCME_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:31:25.565993+00:00
-- url     : https://prove2.me/theorems/796fd383-1976-4685-91f4-917e871e30f5
-- title:
--   Automorphic: conj CME apply
-- statement:
--   The Automorphic construction uses the conj CME apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L20-L20

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
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem GroundTheory.Automorphic.conjCME_apply (k x : G) : conjCME k x = k * x * k⁻¹ := by sorry

attribute [defeq] GroundTheory.Automorphic.conjCME_apply
