-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_eq_zero_of_cob_eq_zero
-- name    : GlobalTheory.PDivGroup.eq_zero_of_cob_eq_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:39:56.210374+00:00
-- url     : https://prove2.me/theorems/5c9ec93f-0e2d-47e5-9a13-9073f583a6f7
-- title:
--   PDiv Group: eq zero of cob eq zero
-- statement:
--   The PDiv Group construction uses the eq zero of cob eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RigOfOmegaInjectiveOfEqZero.lean#L174-L176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToBaseChangePtsBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DUnitMemRangeOfMemKerIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv
variable {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R)

theorem GlobalTheory.PDivGroup.eq_zero_of_cob_eq_zero (hp : (p : R) = 0) {B : G.funs} (hB : G.cob B = 0) : B = 0 := by sorry
