-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_permGL_mul_diagGL
-- name    : GroundTheory.Automorphic.Whittaker.permGL_mul_diagGL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:22.294028+00:00
-- url     : https://prove2.me/theorems/25c3f0ab-6f09-4c66-8344-b56ac6c9849b
-- title:
--   Whittaker: perm GL mul diag GL
-- statement:
--   The Whittaker construction uses the perm GL mul diag GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L357-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L357-L366

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.permGL_mul_diagGL (w : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) :
    permGL F w * Iwasawa.diagGL F n d = Iwasawa.diagGL F n (fun r => d (w⁻¹ r)) * permGL F w := by sorry
