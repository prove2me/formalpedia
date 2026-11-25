-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_pow
-- name    : GroundTheory.Automorphic.HarishChandra.TopClose.pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:12.449488+00:00
-- url     : https://prove2.me/theorems/ba4d8d6c-4e08-4a71-905e-52976c83c712
-- title:
--   Top Close: pow
-- statement:
--   The Top Close construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L85-L91

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

theorem GroundTheory.Automorphic.HarishChandra.TopClose.pow {k : ℕ} {a b : MvPolynomial (Fin n) ℂ} (h : TopClose k a b) (c : ℕ) :
    TopClose (c * k) (a ^ c) (b ^ c) := by sorry
