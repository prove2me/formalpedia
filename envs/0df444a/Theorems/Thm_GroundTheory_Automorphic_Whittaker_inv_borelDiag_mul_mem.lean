-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_inv_borelDiag_mul_mem
-- name    : GroundTheory.Automorphic.Whittaker.inv_borelDiag_mul_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:41:22.606698+00:00
-- url     : https://prove2.me/theorems/2c31940d-b62d-432d-b71c-f966512f7d81
-- title:
--   Whittaker: inv borel Diag mul mem
-- statement:
--   The Whittaker construction uses the inv borel Diag mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L348-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L348-L355

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

theorem GroundTheory.Automorphic.Whittaker.inv_borelDiag_mul_mem {b : GL (Fin n) F} (hb : b ∈ borel n F) :
    (Iwasawa.diagGL F n (borelDiag hb))⁻¹ * b ∈ Iwasawa.unipotent F n := by sorry
