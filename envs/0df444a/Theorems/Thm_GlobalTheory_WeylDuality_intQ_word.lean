-- Prove2me | Theorems.Thm_GlobalTheory_WeylDuality_intQ_word
-- name    : GlobalTheory.WeylDuality.intQ_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:58.081744+00:00
-- url     : https://prove2.me/theorems/c9f2d730-bcea-4c72-923d-cbbb2cf2dff9
-- title:
--   Weyl Duality: int Q word
-- statement:
--   The Weyl Duality construction uses the int Q word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ApplyWordMemDualWeyl.lean#L59-L61

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

theorem GlobalTheory.WeylDuality.intQ_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ)) :
    intQ r n (applyWord ℤ w (hw ℤ hn ν)) = applyWord ℚ w (hw ℚ hn ν) := by sorry
