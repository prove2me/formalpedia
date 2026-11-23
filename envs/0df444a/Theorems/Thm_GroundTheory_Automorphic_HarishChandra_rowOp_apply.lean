-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rowOp_apply
-- name    : GroundTheory.Automorphic.HarishChandra.rowOp_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:44.592224+00:00
-- url     : https://prove2.me/theorems/ec433ca1-0fe0-4335-bab7-1093eb291405
-- title:
--   Harish Chandra: row Op apply
-- statement:
--   The Harish Chandra construction uses the row Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RepBase.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RepBase.lean#L13-L15

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
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

theorem GroundTheory.Automorphic.HarishChandra.rowOp_apply (i j : Fin n) (f : Poly n) :
    rowOp i j f = ∑ k : Fin n, MvPolynomial.X (i, k) * MvPolynomial.pderiv (j, k) f := by sorry
