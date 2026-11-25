-- Prove2me | Theorems.Thm_GlobalTheory_Nef_Kron_ev_X_pow_mul
-- name    : GlobalTheory.Nef.Kron.ev_X_pow_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:50.621675+00:00
-- url     : https://prove2.me/theorems/abb38745-5f18-49f3-badb-feb2a30f512f
-- title:
--   Kron: ev X pow mul
-- statement:
--   The Kron construction uses the ev X pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsRatOfHankelEventuallyZero.lean#L40-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRatOfHankelEventuallyZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.Kron
open Polynomial
variable {F : Type} [Field F] (c : ℕ → F)

theorem GlobalTheory.Nef.Kron.ev_X_pow_mul (m : ℕ) (q : F[X]) :
    ev c (q * X ^ m) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * c (m + j) := by sorry
