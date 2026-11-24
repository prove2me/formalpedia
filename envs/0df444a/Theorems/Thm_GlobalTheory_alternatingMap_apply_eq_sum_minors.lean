-- Prove2me | Theorems.Thm_GlobalTheory_alternatingMap_apply_eq_sum_minors
-- name    : GlobalTheory.alternatingMap_apply_eq_sum_minors
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:50.194674+00:00
-- url     : https://prove2.me/theorems/6ab40cc2-3407-4ea8-96aa-2abc80f1e5d1
-- title:
--   Global Theory: alternating Map apply eq sum minors
-- statement:
--   The Global Theory construction uses the alternating Map apply eq sum minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L22-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {R : Type*} [CommRing R]

theorem GlobalTheory.alternatingMap_apply_eq_sum_minors {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    {M : Type*} [AddCommGroup M] [Module R M] (f : (n → R) [⋀^Fin i]→ₗ[R] M)
    (A : Fin i → n → R) :
    f A = ∑ S : Set.powersetCard n i,
      ((Matrix.of A).submatrix id (subsetEnum S)).det • f (fun a => Pi.single (subsetEnum S a) 1) := by sorry
