-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_vanishingOn
-- name    : GroundTheory.Automorphic.Whittaker.mem_vanishingOn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:22.463629+00:00
-- url     : https://prove2.me/theorems/47b70683-bd56-4c2b-b9f2-4fa0cd73b171
-- title:
--   Whittaker: mem vanishing On
-- statement:
--   The Whittaker construction uses the mem vanishing On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L35-L36

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyConstantCompact
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology
variable {X : Type*} [TopologicalSpace X]
omit [TopologicalSpace X]

theorem GroundTheory.Automorphic.Whittaker.mem_vanishingOn {Z : Set X} {f : X → ℂ} : f ∈ vanishingOn Z ↔ ∀ x ∈ Z, f x = 0 := by sorry
