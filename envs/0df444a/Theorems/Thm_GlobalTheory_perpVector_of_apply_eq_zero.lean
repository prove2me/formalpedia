-- Prove2me | Theorems.Thm_GlobalTheory_perpVector_of_apply_eq_zero
-- name    : GlobalTheory.perpVector_of_apply_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:08.174715+00:00
-- url     : https://prove2.me/theorems/e1cf5a28-8300-441d-8739-00249ce61a22
-- title:
--   Global Theory: perp Vector of apply eq zero
-- statement:
--   The Global Theory construction uses the perp Vector of apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L35-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.perpVector_of_apply_eq_zero (ε : ι → Module.Dual R M) (e' : ι → M) {g : M}
    (hg : ∀ a, ε a g = 0) : perpVector ε e' g = (pairingMatrix ε e').det • g := by sorry
