-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_esymm_mem_adjoin_psum
-- name    : GroundTheory.Automorphic.HarishChandra.esymm_mem_adjoin_psum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:47.400936+00:00
-- url     : https://prove2.me/theorems/515168a3-527d-417d-a9b9-a1785dde8a64
-- title:
--   Harish Chandra: esymm mem adjoin psum
-- statement:
--   The Harish Chandra construction uses the esymm mem adjoin psum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L11-L35

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

theorem GroundTheory.Automorphic.HarishChandra.esymm_mem_adjoin_psum (k : ℕ) (hk : k ≤ n) :
    esymm (Fin n) ℂ k ∈ Algebra.adjoin ℂ (Set.range (psumFin (n := n))) := by sorry
