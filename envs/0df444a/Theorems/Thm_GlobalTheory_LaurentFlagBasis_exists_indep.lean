-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFlagBasis_exists_indep
-- name    : GlobalTheory.LaurentFlagBasis.exists_indep
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:45:16.43819+00:00
-- url     : https://prove2.me/theorems/4caad086-3c74-4359-8054-c03b7c1d74f4
-- title:
--   Laurent Flag Basis: exists indep
-- statement:
--   The Laurent Flag Basis construction uses the exists indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L37-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L37-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdaptedIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory GlobalTheory.LaurentFlagBasis
variable {F : Type} [Field F]

theorem GlobalTheory.LaurentFlagBasis.exists_indep {n : ℕ} : ∀ (d : ℕ) (U : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)),
    d ≤ Module.finrank (LaurentSeries F) U →
    ∃ y : Fin d → (Fin n → PowerSeries F), (∀ b, lift (y b) ∈ U) ∧
      LinearIndependent F (fun b => red (y b))
  := by sorry
