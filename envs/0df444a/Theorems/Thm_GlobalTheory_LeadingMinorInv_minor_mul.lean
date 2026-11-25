-- Prove2me | Theorems.Thm_GlobalTheory_LeadingMinorInv_minor_mul
-- name    : GlobalTheory.LeadingMinorInv.minor_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:39.895898+00:00
-- url     : https://prove2.me/theorems/c1f1b738-60a2-4f85-99b7-6f211af83d90
-- title:
--   Leading Minor Inv: minor mul
-- statement:
--   The Leading Minor Inv construction uses the minor mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingMinorInvariant.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingMinorInvariant.lean#L15-L42

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants

theorem GlobalTheory.LeadingMinorInv.minor_mul {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by sorry
