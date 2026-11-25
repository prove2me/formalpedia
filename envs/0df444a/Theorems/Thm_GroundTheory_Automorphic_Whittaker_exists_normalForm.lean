-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_exists_normalForm
-- name    : GroundTheory.Automorphic.Whittaker.exists_normalForm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:28:50.634372+00:00
-- url     : https://prove2.me/theorems/620f7f01-09ab-4aae-b4b9-5187b7d4bc92
-- title:
--   Whittaker: exists normal Form
-- statement:
--   The Whittaker construction uses the exists normal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L389-L392
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L389-L392

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

theorem GroundTheory.Automorphic.Whittaker.exists_normalForm (g : GL (Fin n) F) :
    ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
      g = u * Iwasawa.diagGL F n t * permGL F (bruhatCell g) * v := by sorry
