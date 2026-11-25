-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_iff_normalForm
-- name    : GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:31.317424+00:00
-- url     : https://prove2.me/theorems/3b2014f8-8228-4c02-bad3-28be678b1d94
-- title:
--   Whittaker: mem double Coset iff normal Form
-- statement:
--   The Whittaker construction uses the mem double Coset iff normal Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L368-L387
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L368-L387

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

theorem GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) ↔
      ∃ u ∈ Iwasawa.unipotent F n, ∃ t : Fin n → Fˣ, ∃ v ∈ Iwasawa.unipotent F n,
        g = u * Iwasawa.diagGL F n t * permGL F w * v := by sorry
