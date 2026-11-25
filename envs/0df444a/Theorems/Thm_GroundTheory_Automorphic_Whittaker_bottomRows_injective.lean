-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bottomRows_injective
-- name    : GroundTheory.Automorphic.Whittaker.bottomRows_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:24.335312+00:00
-- url     : https://prove2.me/theorems/d4851ae8-7bff-4d95-85bf-471e4fe3869a
-- title:
--   Whittaker: bottom Rows injective
-- statement:
--   The Whittaker construction uses the bottom Rows injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L411-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L411-L414

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

theorem GroundTheory.Automorphic.Whittaker.bottomRows_injective (k : Fin n) : Function.Injective (bottomRows k) := by sorry
