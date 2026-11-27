-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_eq_borelGL_mul_kGL
-- name    : GroundTheory.Automorphic.GL2Classical.eq_borelGL_mul_kGL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:51.517839+00:00
-- url     : https://prove2.me/theorems/9a3ba2d1-d2c8-467e-9259-71365947b231
-- title:
--   GL2 Classical: eq borel GL mul k GL
-- statement:
--   The GL2 Classical construction uses the eq borel GL mul k GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L87-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L87-L108

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

theorem GroundTheory.Automorphic.GL2Classical.eq_borelGL_mul_kGL {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    h = borelGL (h • I) * kGL (denom h (I : ℂ)) (denom_ne_zero h I) := by sorry
