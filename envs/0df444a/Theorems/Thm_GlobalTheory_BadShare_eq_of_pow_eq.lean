-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_eq_of_pow_eq
-- name    : GlobalTheory.BadShare.eq_of_pow_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:07.60586+00:00
-- url     : https://prove2.me/theorems/90c0c10c-c33c-48b6-8173-42cd8afe5749
-- title:
--   Bad Share: eq of pow eq
-- statement:
--   The Bad Share construction uses the eq of pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SamePartIffOfNeZero.lean#L86-L97

import Mathlib
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}
open Polynomial Classical
variable (g : ℕ) [Fact g.Prime]
variable {k : Type} [Field k] {l : ℕ}

theorem GlobalTheory.BadShare.eq_of_pow_eq {M a : ℕ} (hM : M.Coprime l) {x y : k} (hx : x ^ M = 1)
    (hy : y ^ M = 1) (hM0 : M ≠ 0) (h : x ^ (l ^ a) = y ^ (l ^ a)) : x = y := by sorry
