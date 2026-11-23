-- Prove2me | Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
-- name    : GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:23.983875+00:00
-- url     : https://prove2.me/theorems/1a17905d-1fd0-41c1-bd10-357b5a5c911f
-- title:
--   Global Theory: quotient Map CSup Span Lin Form Equiv mk
-- statement:
--   The Global Theory construction uses the quotient Map CSup Span Lin Form Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L371-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L371-L374

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

theorem GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk (S : Set ι) (I : Ideal R)
    (p : MvPolynomial (ι × J) R) :
    quotientMapCSupSpanLinFormEquiv u hu S I (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (Ideal.Quotient.mk I) (linFormElim u hu S p) := by sorry

attribute [defeq] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
