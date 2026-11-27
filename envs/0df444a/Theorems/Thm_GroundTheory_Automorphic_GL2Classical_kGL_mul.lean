-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_kGL_mul
-- name    : GroundTheory.Automorphic.GL2Classical.kGL_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:33.192942+00:00
-- url     : https://prove2.me/theorems/8f285338-0141-44da-878a-03b01288f510
-- title:
--   GL2 Classical: k GL mul
-- statement:
--   The GL2 Classical construction uses the k GL mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L43-L47

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Iwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix UpperHalfPlane
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical

theorem GroundTheory.Automorphic.GL2Classical.kGL_mul (w₁ w₂ : ℂ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    kGL w₁ hw₁ * kGL w₂ hw₂ = kGL (w₁ * w₂) (mul_ne_zero hw₁ hw₂) := by sorry
