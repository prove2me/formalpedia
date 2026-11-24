-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_det_kGL
-- name    : GroundTheory.Automorphic.GL2Classical.det_kGL
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:00.252329+00:00
-- url     : https://prove2.me/theorems/e4ea65f8-bd0c-437e-9279-e2fbe3369e83
-- title:
--   GL2 Classical: det k GL
-- statement:
--   The GL2 Classical construction uses the det k GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L26-L27

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

theorem GroundTheory.Automorphic.GL2Classical.det_kGL (w : ℂ) (hw : w ≠ 0) : (kGL w hw).det.val = Complex.normSq w := by sorry
