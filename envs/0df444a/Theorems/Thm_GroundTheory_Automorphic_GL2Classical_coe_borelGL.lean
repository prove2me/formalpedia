-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GL2Classical_coe_borelGL
-- name    : GroundTheory.Automorphic.GL2Classical.coe_borelGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:02.925167+00:00
-- url     : https://prove2.me/theorems/98e2296a-5e3a-43ab-b778-b4b023b75785
-- title:
--   GL2 Classical: coe borel GL
-- statement:
--   The GL2 Classical construction uses the coe borel GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2Classical/Iwasawa.lean#L55-L57

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

theorem GroundTheory.Automorphic.GL2Classical.coe_borelGL (z : ℍ) :
    (borelGL z : Matrix (Fin 2) (Fin 2) ℝ) = !![z.im, z.re; 0, 1] := by sorry

attribute [defeq] GroundTheory.Automorphic.GL2Classical.coe_borelGL
