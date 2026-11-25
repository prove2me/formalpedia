-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_prodFrom_eq_mul
-- name    : GroundTheory.Automorphic.Whittaker.prodFrom_eq_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:49.947486+00:00
-- url     : https://prove2.me/theorems/02ca5cd1-7b72-4c7b-af52-460d06724436
-- title:
--   Whittaker: prod From eq mul
-- statement:
--   The Whittaker construction uses the prod From eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L506-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L506-L515

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

theorem GroundTheory.Automorphic.Whittaker.prodFrom_eq_mul (t : Fin n → Fˣ) (x : Fin n) :
    prodFrom t x.val = (t x : F) * prodFrom t (x.val + 1) := by sorry
