-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_normalForm
-- name    : GroundTheory.Automorphic.Whittaker.cellMinor_normalForm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:44.714686+00:00
-- url     : https://prove2.me/theorems/4c4ea55a-1aab-4b08-b12d-078009ebc955
-- title:
--   Whittaker: cell Minor normal Form
-- statement:
--   The Whittaker construction uses the cell Minor normal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L465-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L465-L486

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

theorem GroundTheory.Automorphic.Whittaker.cellMinor_normalForm (w : Equiv.Perm (Fin n)) {u v : GL (Fin n) F}
    (hu : u ∈ Iwasawa.unipotent F n) (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) :
    cellMinor w (u * Iwasawa.diagGL F n t * permGL F w * v) =
      fun k => ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) := by sorry
