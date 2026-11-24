-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_comm_self
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_comm_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:32:14.579116+00:00
-- url     : https://prove2.me/theorems/c64ab3f5-2c0f-444d-b913-5db759e746b0
-- title:
--   Harish Chandra: row Op comm self
-- statement:
--   The Harish Chandra construction uses the row Op comm self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L43-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L43-L59

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.rowOp_comm_self (a i j : Fin n) :
    rowOp a a * rowOp i j =
      rowOp i j * rowOp a a + ((if i = a then 1 else 0) - (if j = a then 1 else 0) : ℂ) • rowOp i j := by sorry
