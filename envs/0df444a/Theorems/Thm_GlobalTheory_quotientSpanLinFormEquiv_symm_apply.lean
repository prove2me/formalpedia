-- Prove2me | Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_symm_apply
-- name    : GlobalTheory.quotientSpanLinFormEquiv_symm_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:49:57.235797+00:00
-- url     : https://prove2.me/theorems/ec92d3c2-2fcf-5fae-8b5e-c58a11378389
-- title:
--   Global Theory: quotient Span Lin Form Equiv symm apply
-- statement:
--   The Global Theory construction uses the quotient Span Lin Form Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L357-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L357-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))

theorem GlobalTheory.quotientSpanLinFormEquiv_symm_apply (S : Set ι)
    (p : MvPolynomial {x : ι × J // x ∉ elimIndices S j₀} R) :
    (quotientSpanLinFormEquiv u hu S).symm p = Ideal.Quotient.mk _ (rename Subtype.val p) := by sorry
