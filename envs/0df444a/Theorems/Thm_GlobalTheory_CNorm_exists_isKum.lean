-- Prove2me | Theorems.Thm_GlobalTheory_CNorm_exists_isKum
-- name    : GlobalTheory.CNorm.exists_isKum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:29.926262+00:00
-- url     : https://prove2.me/theorems/9d7c7313-d94c-48df-9b44-9eb1b44b6b51
-- title:
--   CNorm: exists is Kum
-- statement:
--   The CNorm construction uses the exists is Kum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsKum.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsKum.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsKum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm

theorem GlobalTheory.CNorm.exists_isKum : ∀ (p : ℕ) (F : Type) [Field F] [CharZero F] (ζ δ : F), p.Prime → IsPrimitiveRoot ζ p → (∀ r : F, r ^ p ≠ δ) → ∃ (E : Type) (_ : Field E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ := by sorry
