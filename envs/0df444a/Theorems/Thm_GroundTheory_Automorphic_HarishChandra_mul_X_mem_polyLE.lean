-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mul_X_mem_polyLE
-- name    : GroundTheory.Automorphic.HarishChandra.mul_X_mem_polyLE
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:18.843859+00:00
-- url     : https://prove2.me/theorems/0e08c142-92e9-463e-b98a-0539e00c4269
-- title:
--   Harish Chandra: mul X mem poly LE
-- statement:
--   The Harish Chandra construction uses the mul X mem poly LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L175-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/LeadingTerm.lean#L175-L178

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Projection
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_LeadingTerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
attribute [local instance 100] LieRing.ofAssociativeRing
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.mul_X_mem_polyLE {d : ℕ} {p : MvPolynomial (Fin n) ℂ} (hp : p ∈ polyLE n d) (i : Fin n) :
    p * X i ∈ polyLE n (d + 1) := by sorry
