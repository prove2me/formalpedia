-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_blockW_ne_nil
-- name    : GroundTheory.Automorphic.HarishChandra.blockW_ne_nil
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:07:03.561616+00:00
-- url     : https://prove2.me/theorems/893c999b-81d9-4fd6-97a3-7df83895834a
-- title:
--   Harish Chandra: block W ne nil
-- statement:
--   The Harish Chandra construction uses the block W ne nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Triangular.lean#L78-L85

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

theorem GroundTheory.Automorphic.HarishChandra.blockW_ne_nil {l : List (Fin n × Fin n)} {m : Fin n × Fin n →₀ ℕ} {a : Fin n × Fin n}
    (ha : a ∈ l) (hm : m a ≠ 0) : blockW l m ≠ [] := by sorry
