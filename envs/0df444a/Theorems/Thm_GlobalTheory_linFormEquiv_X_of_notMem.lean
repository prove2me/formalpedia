-- Prove2me | Theorems.Thm_GlobalTheory_linFormEquiv_X_of_notMem
-- name    : GlobalTheory.linFormEquiv_X_of_notMem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:07:16.686125+00:00
-- url     : https://prove2.me/theorems/95cfc3ea-8dc6-4138-a267-16a6a4a4677d
-- title:
--   Global Theory: lin Form Equiv X of not Mem
-- statement:
--   The Global Theory construction uses the lin Form Equiv X of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L251-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsWeaklyRegularMapCAppendMapLinForm.lean#L251-L253

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

theorem GlobalTheory.linFormEquiv_X_of_notMem {S : Set ι} {x : ι × J} (hx : x ∉ elimIndices S j₀) :
    linFormEquiv u S j₀ hu (X x) = X x := by sorry
