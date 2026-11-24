-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_inV_bDual
-- name    : GlobalTheory.WeylDuality.inV_bDual
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:55:40.351841+00:00
-- url     : https://prove2.me/theorems/8d8c60c4-fcd9-4b3f-8c8d-ed8945a78cfa
-- title:
--   Weyl Duality: in V b Dual
-- statement:
--   The Weyl Duality construction uses the in V b Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L227-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L227-L246

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

theorem GlobalTheory.WeylDuality.inV_bDual {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (M : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ))
    (hM : ∀ Q ∈ M, Q ∈ dualWeyl ℚ r n ν) :
    inV ν (bDual r n hn ν M) = (normB hn ν).dualSubmodule (inV ν M) := by sorry
