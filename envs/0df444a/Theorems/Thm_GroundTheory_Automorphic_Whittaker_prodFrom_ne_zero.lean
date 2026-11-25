-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_prodFrom_ne_zero
-- name    : GroundTheory.Automorphic.Whittaker.prodFrom_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:53.160689+00:00
-- url     : https://prove2.me/theorems/a363d9cc-4c7f-4cca-a1fe-c1b41fcd98e6
-- title:
--   Whittaker: prod From ne zero
-- statement:
--   The Whittaker construction uses the prod From ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L517-L518
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L517-L518

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

theorem GroundTheory.Automorphic.Whittaker.prodFrom_ne_zero (t : Fin n → Fˣ) (s : ℕ) : prodFrom t s ≠ 0 := by sorry
