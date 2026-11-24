-- Prove2me | Theorems.Thm_GlobalTheory_dlog_zpow
-- name    : GlobalTheory.dlog_zpow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:09.205744+00:00
-- url     : https://prove2.me/theorems/671879e9-2d2a-44ad-a2e3-b5fed4071ac2
-- title:
--   Global Theory: dlog zpow
-- statement:
--   The Global Theory construction uses the dlog zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L160-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K : Type*) {F : Type*} [CommRing K] [Field F] [Algebra K F] {p : ℕ}

theorem GlobalTheory.dlog_zpow {x : F} (hx : x ≠ 0) (m : ℤ) :
    (x ^ m)⁻¹ • D K F (x ^ m) = m • x⁻¹ • D K F x := by sorry
