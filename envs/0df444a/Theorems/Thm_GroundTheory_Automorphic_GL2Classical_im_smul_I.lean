-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_im_smul_I
-- name    : GroundTheory.Automorphic.GL2Classical.im_smul_I
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:29:45.192509+00:00
-- url     : https://prove2.me/theorems/726094d4-174c-495b-aee3-f0a7e1490db8
-- title:
--   GL2 Classical: im smul I
-- statement:
--   The GL2 Classical construction uses the im smul I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L83-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L83-L85

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

theorem GroundTheory.Automorphic.GL2Classical.im_smul_I {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) :
    (h • I).im = h.det.val / Complex.normSq (denom h (I : ℂ)) := by sorry
