-- Prove2me | Theorems.Thm_GlobalTheory_isPrime_span_linForm
-- name    : GlobalTheory.isPrime_span_linForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:06.049334+00:00
-- url     : https://prove2.me/theorems/cad7de77-be04-4f3f-a595-e9b854916764
-- title:
--   Global Theory: is Prime span lin Form
-- statement:
--   The Global Theory construction uses the is Prime span lin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L387-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L387-L390

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
include hu

theorem GlobalTheory.isPrime_span_linForm [IsDomain R] (S : Set ι) :
    (Ideal.span (linForm u '' S)).IsPrime := by sorry
