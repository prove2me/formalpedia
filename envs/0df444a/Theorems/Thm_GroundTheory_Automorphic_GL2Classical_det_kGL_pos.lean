-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_kGL_pos
-- name    : GroundTheory.Automorphic.GL2Classical.det_kGL_pos
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:30:17.296272+00:00
-- url     : https://prove2.me/theorems/c3353fa9-7745-4782-8a8b-760874db2ada
-- title:
--   GL2 Classical: det k GL pos
-- statement:
--   The GL2 Classical construction uses the det k GL pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L29-L31

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

theorem GroundTheory.Automorphic.GL2Classical.det_kGL_pos (w : ℂ) (hw : w ≠ 0) : 0 < (kGL w hw).det.val := by sorry
