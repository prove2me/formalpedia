-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_vanishingOn_anti
-- name    : GroundTheory.Automorphic.Whittaker.vanishingOn_anti
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:19.441352+00:00
-- url     : https://prove2.me/theorems/b9fe1dca-560c-54b9-a3bb-b14426fe8d0a
-- title:
--   Whittaker: vanishing On anti
-- statement:
--   The Whittaker construction uses the vanishing On anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L39-L40

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

theorem GroundTheory.Automorphic.Whittaker.vanishingOn_anti {Z Z' : Set X} (h : Z ⊆ Z') : vanishingOn Z' ≤ vanishingOn Z := by sorry
