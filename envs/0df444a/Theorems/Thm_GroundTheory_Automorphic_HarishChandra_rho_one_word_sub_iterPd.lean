-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_rho_one_word_sub_iterPd
-- name    : GroundTheory.Automorphic.HarishChandra.rho_one_word_sub_iterPd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:53.58959+00:00
-- url     : https://prove2.me/theorems/82c905b8-0078-4529-94f8-323ed55ebe52
-- title:
--   Harish Chandra: rho one word sub iter Pd
-- statement:
--   The Harish Chandra construction uses the rho one word sub iter Pd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L276-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/RhoOneEqZeroOfRhoZeroEqZero.lean#L276-L298

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RhoOneEqZeroOfRhoZeroEqZero
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

theorem GroundTheory.Automorphic.HarishChandra.rho_one_word_sub_iterPd (w : List (Fin n × Fin n)) {t : ℕ} {f : Poly n}
    (hw : w.length ≤ t) (hf : f ∈ geDeg t) :
    rho 1 (word w) f - iterPd w f ∈ geDeg (t - w.length + 1) := by sorry
