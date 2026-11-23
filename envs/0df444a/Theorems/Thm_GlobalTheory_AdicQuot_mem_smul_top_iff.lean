-- Prove2me | Theorems.Thm_GlobalTheory_AdicQuot_mem_smul_top_iff
-- name    : GlobalTheory.AdicQuot.mem_smul_top_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:36.139796+00:00
-- url     : https://prove2.me/theorems/69328f8b-b6fb-4f99-a524-59761b40fed9
-- title:
--   Adic Quot: mem smul top iff
-- statement:
--   The Adic Quot construction uses the mem smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)

theorem GlobalTheory.AdicQuot.mem_smul_top_iff (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by sorry
