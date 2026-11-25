-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_congruenceSubgroup_one_le_iwahori
-- name    : GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_one_le_iwahori
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:57.700803+00:00
-- url     : https://prove2.me/theorems/ab703cb8-e7e8-4aff-8969-3b7c771e50d0
-- title:
--   GLn Local: congruence Subgroup one le iwahori
-- statement:
--   The GLn Local construction uses the congruence Subgroup one le iwahori property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L90-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L90-L104

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
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
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.GLnLocal.congruenceSubgroup_one_le_iwahori : congruenceSubgroup F n 1 ≤ iwahori F n := by sorry
