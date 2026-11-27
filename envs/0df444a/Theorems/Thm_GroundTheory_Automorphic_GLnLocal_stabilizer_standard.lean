-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_stabilizer_standard
-- name    : GroundTheory.Automorphic.GLnLocal.stabilizer_standard
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:43.626774+00:00
-- url     : https://prove2.me/theorems/aee5caaa-4773-58f0-9389-86358e5ed9d5
-- title:
--   GLn Local: stabilizer standard
-- statement:
--   The GLn Local construction uses the stabilizer standard property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L145-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GLnLattice.lean#L145-L148

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
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
open scoped Pointwise Matrix
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)

theorem GroundTheory.Automorphic.GLnLocal.stabilizer_standard :
    MulAction.stabilizer (GL (Fin n) F) (standard F n) = integralGL F n := by sorry
