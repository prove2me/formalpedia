-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_le
-- name    : GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:20:18.803793+00:00
-- url     : https://prove2.me/theorems/df644cf7-d74e-4281-ad7b-108638e44af1
-- title:
--   GLn Local: congruence Subgroup le
-- statement:
--   The GLn Local construction uses the congruence Subgroup le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L209-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L209-L210

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Topology Filter Set
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_le (m : ℕ) : congruenceSubgroup F n m ≤ integralGL F n := by sorry
