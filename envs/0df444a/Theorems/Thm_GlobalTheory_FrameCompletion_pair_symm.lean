-- Prove2me | Theorems.Thm_GlobalTheory_FrameCompletion_pair_symm
-- name    : GlobalTheory.FrameCompletion.pair_symm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:10.299583+00:00
-- url     : https://prove2.me/theorems/0b4747dc-026a-47fc-b37a-ac8a26f84f95
-- title:
--   Frame Completion: pair symm
-- statement:
--   The Frame Completion construction uses the pair symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DoubledLatticePrimitiveIsotropicFrameCompletion.lean#L59-L61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DoubledLatticePrimitiveIsotropicFrameCompletion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.FrameCompletion
variable {L : Type} [Field L] {σ : L →+* L}

theorem GlobalTheory.FrameCompletion.pair_symm (hσσ : ∀ x, σ (σ x) = x) {n : ℕ} {κ μ : Type} (X : Matrix (Fin n ⊕ Fin n) κ L)
    (X' : Matrix (Fin n ⊕ Fin n) μ L) : cT σ (cT σ X * gramQ L n * X') = cT σ X' * gramQ L n * X := by sorry
