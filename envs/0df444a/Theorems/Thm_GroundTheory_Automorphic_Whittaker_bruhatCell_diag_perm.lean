-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_diag_perm
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_diag_perm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:18.595026+00:00
-- url     : https://prove2.me/theorems/8b685c03-def2-4011-9395-92a408d10123
-- title:
--   Whittaker: bruhat Cell diag perm
-- statement:
--   The Whittaker construction uses the bruhat Cell diag perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L399-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L399-L402

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

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_diag_perm (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (Iwasawa.diagGL F n t * permGL F w) = w := by sorry
