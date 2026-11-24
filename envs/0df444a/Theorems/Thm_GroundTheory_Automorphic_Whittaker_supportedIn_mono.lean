-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_mono
-- name    : GroundTheory.Automorphic.Whittaker.supportedIn_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:21.782029+00:00
-- url     : https://prove2.me/theorems/a3c62389-8d36-447b-a61b-57fb025872e6
-- title:
--   Whittaker: supported In mono
-- statement:
--   The Whittaker construction uses the supported In mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerLSpace.lean#L25-L26

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

theorem GroundTheory.Automorphic.Whittaker.supportedIn_mono {U V : Set X} (h : U ⊆ V) : supportedIn U ≤ supportedIn V := by sorry
