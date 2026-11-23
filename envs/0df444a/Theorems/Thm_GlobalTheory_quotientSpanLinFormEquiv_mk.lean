-- Prove2me | Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- name    : GlobalTheory.quotientSpanLinFormEquiv_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:37.191768+00:00
-- url     : https://prove2.me/theorems/58278bfa-6fd7-4632-b147-bc29951693de
-- title:
--   Global Theory: quotient Span Lin Form Equiv mk
-- statement:
--   The Global Theory construction uses the quotient Span Lin Form Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L354-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L354-L355

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

theorem GlobalTheory.quotientSpanLinFormEquiv_mk (S : Set ι) (p : MvPolynomial (ι × J) R) :
    quotientSpanLinFormEquiv u hu S (Ideal.Quotient.mk _ p) = linFormElim u hu S p := by sorry

attribute [defeq] GlobalTheory.quotientSpanLinFormEquiv_mk
