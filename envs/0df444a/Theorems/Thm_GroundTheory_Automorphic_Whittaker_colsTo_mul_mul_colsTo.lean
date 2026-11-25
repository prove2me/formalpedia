-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_colsTo_mul_mul_colsTo
-- name    : GroundTheory.Automorphic.Whittaker.colsTo_mul_mul_colsTo
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:40:36.611642+00:00
-- url     : https://prove2.me/theorems/213d57bd-1192-4366-ad1e-47f53f9b0065
-- title:
--   Whittaker: cols To mul mul cols To
-- statement:
--   The Whittaker construction uses the cols To mul mul cols To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L114-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L114-L123

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

theorem GroundTheory.Automorphic.Whittaker.colsTo_mul_mul_colsTo {b : Matrix (Fin n) (Fin n) F} (hb : b.IsUpperTriangular)
    (j : Fin n) : colsTo j * b * colsTo j = b * colsTo j := by sorry
