-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_TopClose_mul
-- name    : GroundTheory.Automorphic.HarishChandra.TopClose.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:57.376806+00:00
-- url     : https://prove2.me/theorems/c7abd15c-a101-48f6-ac36-204403fed114
-- title:
--   Top Close: mul
-- statement:
--   The Top Close construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L60-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Symmetric.lean#L60-L83

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

theorem GroundTheory.Automorphic.HarishChandra.TopClose.mul {k l : ℕ} {a b a' b' : MvPolynomial (Fin n) ℂ} (h : TopClose k a b)
    (h' : TopClose l a' b') : TopClose (k + l) (a * a') (b * b') := by sorry
