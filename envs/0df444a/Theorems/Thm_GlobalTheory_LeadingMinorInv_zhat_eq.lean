-- Prove2me | Theorems.Thm_GlobalTheory_LeadingMinorInv_zhat_eq
-- name    : GlobalTheory.LeadingMinorInv.zhat_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:23.236097+00:00
-- url     : https://prove2.me/theorems/27c4712a-a935-4e18-810d-c7c8b66088bb
-- title:
--   Leading Minor Inv: zhat eq
-- statement:
--   The Leading Minor Inv construction uses the zhat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingMinorInvariant.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/LeadingMinorInvariant.lean#L59-L64

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

theorem GlobalTheory.LeadingMinorInv.zhat_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Zhat k r z z' g = (flagMat k r z)ᴴ * (Hpk k r * (g * flagMat k r z')) := by sorry
