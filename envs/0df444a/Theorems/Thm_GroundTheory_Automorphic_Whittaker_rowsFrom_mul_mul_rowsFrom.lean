-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_rowsFrom_mul_mul_rowsFrom
-- name    : GroundTheory.Automorphic.Whittaker.rowsFrom_mul_mul_rowsFrom
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:56.145798+00:00
-- url     : https://prove2.me/theorems/a91894b4-cfa3-4352-8a16-40bc511934af
-- title:
--   Whittaker: rows From mul mul rows From
-- statement:
--   The Whittaker construction uses the rows From mul mul rows From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L103-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L103-L112

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

theorem GroundTheory.Automorphic.Whittaker.rowsFrom_mul_mul_rowsFrom {b : Matrix (Fin n) (Fin n) F} (hb : b.IsUpperTriangular)
    (i : Fin n) : rowsFrom i * b * rowsFrom i = rowsFrom i * b := by sorry
