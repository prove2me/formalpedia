-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_eq_of_laurent_div_iff
-- name    : GroundTheory.Automorphic.GodementJacquet.eq_of_laurent_div_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:29:38.303397+00:00
-- url     : https://prove2.me/theorems/bd28bcb3-60ad-4a77-8178-faad7328e83a
-- title:
--   Godement Jacquet: eq of laurent div iff
-- statement:
--   The Godement Jacquet construction uses the eq of laurent div iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L201-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L201-L226

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial

theorem GroundTheory.Automorphic.GodementJacquet.eq_of_laurent_div_iff {P P' : ℂ[X]} (hP : P.eval 0 = 1) (hP' : P'.eval 0 = 1)
    (h : ∀ R : RatFunc ℂ, (∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P) ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P') : P = P' := by sorry
