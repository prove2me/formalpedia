-- Prove2me | Theorems.Thm_GlobalTheory_LaurentFlagBasis_adapted_integral_basis
-- name    : GlobalTheory.LaurentFlagBasis.adapted_integral_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:45:23.082074+00:00
-- url     : https://prove2.me/theorems/8b0b79b3-79e3-47e5-93c6-d84ca0b0b02f
-- title:
--   Laurent Flag Basis: adapted integral basis
-- statement:
--   The Laurent Flag Basis construction uses the adapted integral basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L120-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdaptedIntegralBasis.lean#L120-L156

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
open GlobalTheory.LaurentFlagBasis

theorem GlobalTheory.LaurentFlagBasis.adapted_integral_basis : ∀ (F : Type) [Field F] (n R : ℕ)
    (W : Fin (R + 1) → Submodule (LaurentSeries F) (Fin n → LaurentSeries F)), Monotone W →
    ∃ g : (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ, ∀ (k : Fin (R + 1)) (j : Fin n),
      (j : ℕ) < Module.finrank (LaurentSeries F) (W k) →
      (fun a => (((g : Matrix (Fin n) (Fin n) (PowerSeries F)) a j : PowerSeries F) :
        LaurentSeries F)) ∈ W k := by sorry
