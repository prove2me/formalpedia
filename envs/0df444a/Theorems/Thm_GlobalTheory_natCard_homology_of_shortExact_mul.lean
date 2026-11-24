-- Prove2me | Theorems.Thm_GlobalTheory_natCard_homology_of_shortExact_mul
-- name    : GlobalTheory.natCard_homology_of_shortExact_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:55.341491+00:00
-- url     : https://prove2.me/theorems/96d2a727-392a-407f-94c0-7f4ab9999e5d
-- title:
--   Global Theory: nat Card homology of short Exact mul
-- statement:
--   The Global Theory construction uses the nat Card homology of short Exact mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMul.lean#L18-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NatCardHomologyOfShortExactMul.lean#L18-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.natCard_homology_of_shortExact_mul : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by sorry
