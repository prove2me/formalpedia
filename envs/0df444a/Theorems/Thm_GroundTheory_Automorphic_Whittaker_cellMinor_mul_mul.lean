-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_cellMinor_mul_mul
-- name    : GroundTheory.Automorphic.Whittaker.cellMinor_mul_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:06.623152+00:00
-- url     : https://prove2.me/theorems/33dc77a3-4a9d-44a0-8c20-4f297271d394
-- title:
--   Whittaker: cell Minor mul mul
-- statement:
--   The Whittaker construction uses the cell Minor mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L547-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L547-L556

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

theorem GroundTheory.Automorphic.Whittaker.cellMinor_mul_mul {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} (hg : bruhatCell g = w)
    {a b : GL (Fin n) F} (ha : a ∈ Iwasawa.unipotent F n) (hb : b ∈ Iwasawa.unipotent F n) :
    cellMinor w (a * g * b) = cellMinor w g := by sorry
