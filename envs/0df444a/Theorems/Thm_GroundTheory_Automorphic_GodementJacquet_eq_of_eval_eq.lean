-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_eq_of_eval_eq
-- name    : GroundTheory.Automorphic.GodementJacquet.eq_of_eval_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:18:45.479556+00:00
-- url     : https://prove2.me/theorems/a74d677d-41d0-4959-ad2a-f453d3debb17
-- title:
--   Godement Jacquet: eq of eval eq
-- statement:
--   The Godement Jacquet construction uses the eq of eval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L89-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJLaurentIdeal.lean#L89-L126

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

theorem GroundTheory.Automorphic.GodementJacquet.eq_of_eval_eq {R₁ R₂ : RatFunc ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x : ℂ, x ≠ 0 → ‖x‖ < ε → R₁.eval (RingHom.id ℂ) x = R₂.eval (RingHom.id ℂ) x) :
    R₁ = R₂ := by sorry
