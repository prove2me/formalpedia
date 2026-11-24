-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_adjoin_eq_symmetricSubalgebra
-- name    : GroundTheory.Automorphic.HarishChandra.adjoin_eq_symmetricSubalgebra
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:46.32242+00:00
-- url     : https://prove2.me/theorems/ba46418f-00b6-44c5-9d66-8ade63e74e86
-- title:
--   Harish Chandra: adjoin eq symmetric Subalgebra
-- statement:
--   The Harish Chandra construction uses the adjoin eq symmetric Subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L201-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L201-L208

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

theorem GroundTheory.Automorphic.HarishChandra.adjoin_eq_symmetricSubalgebra (q : Fin n → MvPolynomial (Fin n) ℂ)
    (hq : ∀ k, (q k).IsSymmetric)
    (hdeg : ∀ k, (q k - psum (Fin n) ℂ ((k : ℕ) + 1)).totalDegree < (k : ℕ) + 1) :
    Algebra.adjoin ℂ (Set.range q) = symmetricSubalgebra (Fin n) ℂ := by sorry
