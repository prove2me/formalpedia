-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_le_rank_iff_exists_det_ne_zero
-- name    : GroundTheory.Automorphic.Whittaker.le_rank_iff_exists_det_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:06.720487+00:00
-- url     : https://prove2.me/theorems/c65b100d-177a-4d93-b067-c5a2b148cc0c
-- title:
--   Whittaker: le rank iff exists det ne zero
-- statement:
--   The Whittaker construction uses the le rank iff exists det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L22-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L22-L44

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

theorem GroundTheory.Automorphic.Whittaker.le_rank_iff_exists_det_ne_zero {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m F) (k : ℕ) :
    k ≤ M.rank ↔ ∃ (A : Matrix (Fin k) m F) (B : Matrix m (Fin k) F), (A * M * B).det ≠ 0 := by sorry
