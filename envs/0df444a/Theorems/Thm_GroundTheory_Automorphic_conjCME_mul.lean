-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conjCME_mul
-- name    : GroundTheory.Automorphic.conjCME_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:08:04.516205+00:00
-- url     : https://prove2.me/theorems/f0168fdb-5ec0-43dc-ace7-f2459d4191b2
-- title:
--   Automorphic: conj CME mul
-- statement:
--   The Automorphic construction uses the conj CME mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraInvariance/Compact.lean#L22-L24

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_trans

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

theorem GroundTheory.Automorphic.conjCME_mul (a b : G) : conjCME (a * b) = (conjCME b).trans (conjCME a) := by sorry
