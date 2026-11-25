-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowDer_apply
-- name    : GroundTheory.Automorphic.HarishChandra.rowDer_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:31:53.747173+00:00
-- url     : https://prove2.me/theorems/d8d4121a-cfee-49a0-bfb4-88266e7e3853
-- title:
--   Harish Chandra: row Der apply
-- statement:
--   The Harish Chandra construction uses the row Der apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L41-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L41-L41

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

theorem GroundTheory.Automorphic.HarishChandra.rowDer_apply (i j : Fin n) (f : Poly n) : rowDer i j f = rowOp i j f := by sorry
