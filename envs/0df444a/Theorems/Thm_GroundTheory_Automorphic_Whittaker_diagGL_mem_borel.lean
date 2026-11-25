-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_diagGL_mem_borel
-- name    : GroundTheory.Automorphic.Whittaker.diagGL_mem_borel
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:56.699988+00:00
-- url     : https://prove2.me/theorems/69b91481-0dfc-4452-bb6f-c895200ae0bd
-- title:
--   Whittaker: diag GL mem borel
-- statement:
--   The Whittaker construction uses the diag GL mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L331-L334

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

theorem GroundTheory.Automorphic.Whittaker.diagGL_mem_borel (t : Fin n → Fˣ) : Iwasawa.diagGL F n t ∈ borel n F := by sorry
