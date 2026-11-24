-- Prove2me | Theorems.Thm_GlobalTheory_CoeffSubring_exists_ringHom_pow
-- name    : GlobalTheory.CoeffSubring.exists_ringHom_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:15:11.166423+00:00
-- url     : https://prove2.me/theorems/b168a797-c615-4486-a617-c1e8c9451876
-- title:
--   Coeff Subring: exists ring Hom pow
-- statement:
--   The Coeff Subring construction uses the exists ring Hom pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DvdOfForallSubMulMem.lean#L11-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DvdOfForallSubMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CoeffSubring
variable {k : Type} [Field k] {p : ℕ} {B : Set k}

theorem GlobalTheory.CoeffSubring.exists_ringHom_pow
    (hB : ∀ (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q), (∀ b ∈ B, g b ^ p = f b) →
      ∃ σ : k →+* Q, (∀ x, σ (x ^ p) = f x) ∧ ∀ b ∈ B, σ b = g b)
    (n : ℕ) (Q : Type) [CommRing Q] (f : k →+* Q) (g : k → Q) (h : ∀ b ∈ B, g b ^ p ^ n = f b) :
    ∃ σ : k →+* Q, (∀ x, σ (x ^ p ^ n) = f x) ∧ ∀ b ∈ B, σ b = g b := by sorry
