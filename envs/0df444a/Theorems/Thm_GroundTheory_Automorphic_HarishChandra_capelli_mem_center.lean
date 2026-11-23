-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_capelli_mem_center
-- name    : GroundTheory.Automorphic.HarishChandra.capelli_mem_center
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:40.885087+00:00
-- url     : https://prove2.me/theorems/ded88fee-3f71-48b0-b90e-9b731a44c8b9
-- title:
--   Harish Chandra: capelli mem center
-- statement:
--   The Harish Chandra construction uses the capelli mem center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Capelli.lean#L19-L26

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.capelli_mem_center (k : ℕ) : capelli (n := n) k ∈ Subalgebra.center ℂ (U n) := by sorry
