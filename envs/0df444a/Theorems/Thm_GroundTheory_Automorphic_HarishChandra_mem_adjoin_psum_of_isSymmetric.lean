-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_mem_adjoin_psum_of_isSymmetric
-- name    : GroundTheory.Automorphic.HarishChandra.mem_adjoin_psum_of_isSymmetric
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:51.913246+00:00
-- url     : https://prove2.me/theorems/dd1286f1-f3a3-4e3e-84b3-57a3f60eb676
-- title:
--   Harish Chandra: mem adjoin psum of is Symmetric
-- statement:
--   The Harish Chandra construction uses the mem adjoin psum of is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L45-L52

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Symmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial Finset
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.mem_adjoin_psum_of_isSymmetric {p : MvPolynomial (Fin n) ℂ} (hp : p.IsSymmetric) :
    p ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by sorry
