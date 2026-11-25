-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_canon_mem_nMinusU
-- name    : GroundTheory.Automorphic.HarishChandra.canon_mem_nMinusU
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:06:52.350555+00:00
-- url     : https://prove2.me/theorems/652a71a6-5d84-4292-ba65-81423aa08a6d
-- title:
--   Harish Chandra: canon mem n Minus U
-- statement:
--   The Harish Chandra construction uses the canon mem n Minus U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L222-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L222-L229

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

theorem GroundTheory.Automorphic.HarishChandra.canon_mem_nMinusU {m : Fin n × Fin n →₀ ℕ} (h : HasLower m) : canon m ∈ nMinusU n := by sorry
