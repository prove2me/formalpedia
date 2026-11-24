-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_applyWord_mem_dualWeyl
-- name    : GlobalTheory.WeylDuality.applyWord_mem_dualWeyl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:55:43.965418+00:00
-- url     : https://prove2.me/theorems/b079317d-e292-4626-9390-d495efd9d7c1
-- title:
--   Weyl Duality: apply Word mem dual Weyl
-- statement:
--   The Weyl Duality construction uses the apply Word mem dual Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L13-L20

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality

theorem GlobalTheory.WeylDuality.applyWord_mem_dualWeyl (R : Type) [CommRing R] {r n : ℕ} (ν : Fin n → ℕ)
    (w : List (Fin r × Fin r × ℕ)) {F : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) :
    applyWord R w F ∈ dualWeyl R r n ν := by sorry
