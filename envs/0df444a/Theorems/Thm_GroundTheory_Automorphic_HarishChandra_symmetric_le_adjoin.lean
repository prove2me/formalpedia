-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_symmetric_le_adjoin
-- name    : GroundTheory.Automorphic.HarishChandra.symmetric_le_adjoin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:30:44.673087+00:00
-- url     : https://prove2.me/theorems/e8207814-317a-42be-a144-2db1b3cde8bb
-- title:
--   Harish Chandra: symmetric le adjoin
-- statement:
--   The Harish Chandra construction uses the symmetric le adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L109-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L109-L199

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

theorem GroundTheory.Automorphic.HarishChandra.symmetric_le_adjoin (q : Fin n → MvPolynomial (Fin n) ℂ) (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) (d : ℕ) :
    ∀ p : MvPolynomial (Fin n) ℂ, p.IsSymmetric → p.totalDegree ≤ d →
      p ∈ Algebra.adjoin ℂ (Set.range q) := by sorry
