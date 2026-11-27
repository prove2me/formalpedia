-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_diag_perm
-- name    : GroundTheory.Automorphic.Whittaker.cellMinor_diag_perm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:19.247486+00:00
-- url     : https://prove2.me/theorems/1466a890-1995-4b9e-b558-b706700487d8
-- title:
--   Whittaker: cell Minor diag perm
-- statement:
--   The Whittaker construction uses the cell Minor diag perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L541-L545
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L541-L545

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

theorem GroundTheory.Automorphic.Whittaker.cellMinor_diag_perm (w : Equiv.Perm (Fin n)) (t : Fin n → Fˣ) :
    cellMinor w (Iwasawa.diagGL F n t * permGL F w) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by sorry
