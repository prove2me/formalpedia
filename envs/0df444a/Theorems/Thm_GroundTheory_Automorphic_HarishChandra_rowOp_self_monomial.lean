-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_self_monomial
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_self_monomial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:13.872728+00:00
-- url     : https://prove2.me/theorems/830869b6-5bf8-4196-9527-0206938c07f1
-- title:
--   Harish Chandra: row Op self monomial
-- statement:
--   The Harish Chandra construction uses the row Op self monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L63-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L63-L76

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

theorem GroundTheory.Automorphic.HarishChandra.rowOp_self_monomial (i : Fin n) (s : Fin n × Fin n →₀ ℕ) (c : ℂ) :
    rowOp i i (monomial s c) = monomial s (c * (rowWt s i : ℂ)) := by sorry
