-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_shift
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_shift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:20.056863+00:00
-- url     : https://prove2.me/theorems/d5a5b0a2-d94d-4286-b35a-41269cfe6493
-- title:
--   Harish Chandra: row Op shift
-- statement:
--   The Harish Chandra construction uses the row Op shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L222-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L222-L267

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

theorem GroundTheory.Automorphic.HarishChandra.rowOp_shift {μ : Fin n → ℕ} {v : Poly n} (hv : wtProj μ v = v) {i j : Fin n} (hij : i < j)
    (hne : rowOp i j v ≠ 0) :
    ∃ μ' : Fin n → ℕ, wtProj μ' (rowOp i j v) = rowOp i j v ∧ ∑ a, μ' a = ∑ a, μ a ∧
      wtHeight μ < wtHeight μ' := by sorry
