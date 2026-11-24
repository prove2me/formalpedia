-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuousSMul_orbit
-- name    : GroundTheory.Automorphic.Whittaker.continuousSMul_orbit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:28.036389+00:00
-- url     : https://prove2.me/theorems/bd7ad6d9-ba68-4ce6-823c-922419b74649
-- title:
--   Whittaker: continuous SMul orbit
-- statement:
--   The Whittaker construction uses the continuous SMul orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L190-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerOrbit.lean#L190-L197

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
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
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
  {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]
  [MulAction H X] [ContinuousSMul H X]
omit [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] [SigmaCompactSpace H]

theorem GroundTheory.Automorphic.Whittaker.continuousSMul_orbit (x₀ : X) : ContinuousSMul H (orbit H x₀) := by sorry
