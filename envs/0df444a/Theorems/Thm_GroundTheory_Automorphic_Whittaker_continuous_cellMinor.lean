-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_continuous_cellMinor
-- name    : GroundTheory.Automorphic.Whittaker.continuous_cellMinor
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:01.253804+00:00
-- url     : https://prove2.me/theorems/fc7fdfd4-faa2-453d-ad93-53f91d2fcced
-- title:
--   Whittaker: continuous cell Minor
-- statement:
--   The Whittaker construction uses the continuous cell Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L428-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L428-L430

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

theorem GroundTheory.Automorphic.Whittaker.continuous_cellMinor [TopologicalSpace F] [IsTopologicalRing F]
    (w : Equiv.Perm (Fin n)) : Continuous (cellMinor (F := F) w) := by sorry
