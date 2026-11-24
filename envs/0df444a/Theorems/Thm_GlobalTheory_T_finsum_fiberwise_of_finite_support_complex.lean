-- Prove2me | Theorems.Thm_GlobalTheory_T_finsum_fiberwise_of_finite_support_complex
-- name    : GlobalTheory.T.finsum_fiberwise_of_finite_support_complex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:39:48.934371+00:00
-- url     : https://prove2.me/theorems/2b158618-105a-4216-8cc9-161f1faf8d2d
-- title:
--   T: finsum fiberwise of finite support complex
-- statement:
--   The T construction uses the finsum fiberwise of finite support complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumFiberwiseOfFiniteSupportComplexStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinsumFiberwiseOfFiniteSupportComplexStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumFiberwiseOfFiniteSupportComplex
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinsumFiberwiseOfFiniteSupportComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finsum_fiberwise_of_finite_support_complex : ∀ {A B : Type} (ρ : A → B) (f : A → ℂ), (Function.support f).Finite → ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by sorry
