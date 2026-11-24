-- Prove2me | Theorems.Thm_GlobalTheory_T_submodule_fg_of_span_eq_top_of_locally_pow_mul_mem
-- name    : GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:19.206698+00:00
-- url     : https://prove2.me/theorems/40eea7e7-cf7e-4146-87ba-d07b28258cb2
-- title:
--   T: submodule fg of span eq top of locally pow mul mem
-- statement:
--   The T construction uses the submodule fg of span eq top of locally pow mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubmoduleFgOfLocallyLeFgStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubmoduleFgOfLocallyLeFgStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubmoduleFgOfLocallyLeFgStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.submodule_fg_of_span_eq_top_of_locally_pow_mul_mem : ∀ {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [IsNoetherianRing R] (M : Submodule R A) (s : Set R), Ideal.span s = ⊤ → (∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) → M.FG := by sorry
