-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_pow_mul_mem_span_of_fg_localizationAway
-- name    : GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:32.080127+00:00
-- url     : https://prove2.me/theorems/40aff238-3dd4-48dd-9067-bc4aa8fc2efe
-- title:
--   T: exists finset pow mul mem span of fg localization Away
-- statement:
--   The T construction uses the exists finset pow mul mem span of fg localization Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgLocalizationAwaySpanFinsetStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgLocalizationAwaySpanFinsetStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgLocalizationAwaySpanFinsetStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_pow_mul_mem_span_of_fg_localizationAway : ∀ {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R'] [IsLocalization.Away (algebraMap R A g) A'], ∀ (N : Submodule R' A'), N.FG → ∃ E : Finset A, ∀ b : A, algebraMap A A' b ∈ N → ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A) := by sorry
