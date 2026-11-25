-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_normalForm
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_normalForm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:25.844215+00:00
-- url     : https://prove2.me/theorems/0d485ba6-0d22-4b74-bb9a-dea4f801deb4
-- title:
--   Whittaker: bruhat Cell normal Form
-- statement:
--   The Whittaker construction uses the bruhat Cell normal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L394-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L394-L397

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

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_normalForm {u v : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n)
    (hv : v ∈ Iwasawa.unipotent F n) (t : Fin n → Fˣ) (w : Equiv.Perm (Fin n)) :
    bruhatCell (u * Iwasawa.diagGL F n t * permGL F w * v) = w := by sorry
