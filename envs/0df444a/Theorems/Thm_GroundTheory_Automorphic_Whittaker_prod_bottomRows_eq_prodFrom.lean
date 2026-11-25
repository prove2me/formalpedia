-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_prod_bottomRows_eq_prodFrom
-- name    : GroundTheory.Automorphic.Whittaker.prod_bottomRows_eq_prodFrom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:59.152794+00:00
-- url     : https://prove2.me/theorems/182b0760-edca-450b-8d36-b7b1c8525643
-- title:
--   Whittaker: prod bottom Rows eq prod From
-- statement:
--   The Whittaker construction uses the prod bottom Rows eq prod From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L491-L504
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L491-L504

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

theorem GroundTheory.Automorphic.Whittaker.prod_bottomRows_eq_prodFrom (t : Fin n → Fˣ) (k : Fin n) :
    ∏ a : Fin (k.val + 1), (t (bottomRows k a) : F) = prodFrom t (n - (k.val + 1)) := by sorry
