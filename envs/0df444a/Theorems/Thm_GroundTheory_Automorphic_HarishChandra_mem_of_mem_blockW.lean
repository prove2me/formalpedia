-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_of_mem_blockW
-- name    : GroundTheory.Automorphic.HarishChandra.mem_of_mem_blockW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:31.195327+00:00
-- url     : https://prove2.me/theorems/8fa9c2cf-daba-4b4b-ad2d-837dd759b767
-- title:
--   Harish Chandra: mem of mem block W
-- statement:
--   The Harish Chandra construction uses the mem of mem block W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L72-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L72-L76

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

theorem GroundTheory.Automorphic.HarishChandra.mem_of_mem_blockW {l : List (Fin n × Fin n)} {m : Fin n × Fin n →₀ ℕ}
    {a : Fin n × Fin n} (ha : a ∈ blockW l m) : a ∈ l ∧ m a ≠ 0 := by sorry
