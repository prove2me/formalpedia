-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_hcEmb_mem_cartanSub
-- name    : GroundTheory.Automorphic.HarishChandra.hcEmb_mem_cartanSub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:07:46.046352+00:00
-- url     : https://prove2.me/theorems/b666aa25-ba68-4e34-8f2e-531a31b37dfa
-- title:
--   Harish Chandra: hc Emb mem cartan Sub
-- statement:
--   The Harish Chandra construction uses the hc Emb mem cartan Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L146-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L146-L148

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_ConstantCoeffRhoOneCanonMonomial
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Triangular
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
open scoped IsMulCommutative

theorem GroundTheory.Automorphic.HarishChandra.hcEmb_mem_cartanSub (p : MvPolynomial (Fin n) ℂ) : hcEmb p ∈ cartanSub n := by sorry
