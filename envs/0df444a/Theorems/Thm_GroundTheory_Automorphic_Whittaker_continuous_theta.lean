-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_theta
-- name    : GroundTheory.Automorphic.Whittaker.continuous_theta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:14.146823+00:00
-- url     : https://prove2.me/theorems/dca17b9f-22b0-44b1-a6f9-cda7cb8e8a8b
-- title:
--   Whittaker: continuous theta
-- statement:
--   The Whittaker construction uses the continuous theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L483-L484
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerGroups.lean#L483-L484

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_NormZpow
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
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
open Matrix DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] {n : ℕ}
variable [IsTopologicalRing F]

theorem GroundTheory.Automorphic.Whittaker.continuous_theta : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := by sorry
