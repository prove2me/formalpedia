-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_normal
-- name    : GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_normal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:41.800318+00:00
-- url     : https://prove2.me/theorems/963783a7-8a75-4e48-a5dc-5d8b4170de01
-- title:
--   GLn Local: congruence Subgroup normal
-- statement:
--   The GLn Local construction uses the congruence Subgroup normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L234-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLocal.lean#L234-L238

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

theorem GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_normal (m : ℕ) :
    ((congruenceSubgroup F n m).subgroupOf (integralGL F n)).Normal := by sorry
