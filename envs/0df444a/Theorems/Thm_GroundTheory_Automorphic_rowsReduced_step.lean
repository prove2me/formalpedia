-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_rowsReduced_step
-- name    : GroundTheory.Automorphic.rowsReduced_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:25.437459+00:00
-- url     : https://prove2.me/theorems/781366b9-c2b4-455c-ab70-d9a239f55850
-- title:
--   Automorphic: rows Reduced step
-- statement:
--   The Automorphic construction uses the rows Reduced step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L94-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteBruhat.lean#L94-L234

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

theorem GroundTheory.Automorphic.rowsReduced_step (h : GL (Fin n) k) (t : ℕ) (ht : t < n)
    (hred : RowsReduced (h : Matrix (Fin n) (Fin n) k) (t + 1)) :
    ∃ b₁ ∈ borel n k, ∃ b₂ ∈ borel n k,
      RowsReduced ((b₁ * h * b₂ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) t := by sorry
