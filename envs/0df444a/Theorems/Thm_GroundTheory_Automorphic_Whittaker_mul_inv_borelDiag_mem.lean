-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mul_inv_borelDiag_mem
-- name    : GroundTheory.Automorphic.Whittaker.mul_inv_borelDiag_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:57:16.642726+00:00
-- url     : https://prove2.me/theorems/0f6017b6-b821-405b-aa07-565a50c4626c
-- title:
--   Whittaker: mul inv borel Diag mem
-- statement:
--   The Whittaker construction uses the mul inv borel Diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L339-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L339-L346

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

theorem GroundTheory.Automorphic.Whittaker.mul_inv_borelDiag_mem {b : GL (Fin n) F} (hb : b ∈ borel n F) :
    b * (Iwasawa.diagGL F n (borelDiag hb))⁻¹ ∈ Iwasawa.unipotent F n := by sorry
