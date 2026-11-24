-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_exists_eq_mul_permGL_of_rowsReduced
-- name    : GroundTheory.Automorphic.exists_eq_mul_permGL_of_rowsReduced
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:34:16.678561+00:00
-- url     : https://prove2.me/theorems/13059c9a-8738-4a32-9083-5b39b5c9d2f0
-- title:
--   Automorphic: exists eq mul perm GL of rows Reduced
-- statement:
--   The Automorphic construction uses the exists eq mul perm GL of rows Reduced property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L236-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L236-L260

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]

theorem GroundTheory.Automorphic.exists_eq_mul_permGL_of_rowsReduced (g : GL (Fin n) k)
    (hred : RowsReduced (g : Matrix (Fin n) (Fin n) k) 0) :
    ∃ σ : Equiv.Perm (Fin n), ∃ b ∈ borel n k, g = b * permGL k σ := by sorry
