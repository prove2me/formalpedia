-- Prove2me | Theorems.Thm_GlobalTheory_ProjBij_one_tmul_eq_zero_iff
-- name    : GlobalTheory.ProjBij.one_tmul_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:01.046467+00:00
-- url     : https://prove2.me/theorems/e2d43530-6ad6-4102-868f-02d7fc5b8ef0
-- title:
--   Proj Bij: one tmul eq zero iff
-- statement:
--   The Proj Bij construction uses the one tmul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BijectiveOfInjectiveModMaximal.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BijectiveOfInjectiveModMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.ProjBij

theorem GlobalTheory.ProjBij.one_tmul_eq_zero_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (m : Ideal R) (x : M) :
    ((1 : R ⧸ m) ⊗ₜ[R] x : (R ⧸ m) ⊗[R] M) = 0 ↔ x ∈ m • (⊤ : Submodule R M) := by sorry
