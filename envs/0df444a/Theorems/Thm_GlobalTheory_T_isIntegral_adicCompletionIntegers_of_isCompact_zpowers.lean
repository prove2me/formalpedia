-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegral_adicCompletionIntegers_of_isCompact_zpowers
-- name    : GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:34:00.810074+00:00
-- url     : https://prove2.me/theorems/ec3bd843-f006-5978-b8d5-60325fb5409a
-- title:
--   T: is Integral adic Completion Integers of is Compact zpowers
-- statement:
--   The T construction uses the is Integral adic Completion Integers of is Compact zpowers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowersStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowersStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)), IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E)))) → IsIntegral (w.adicCompletionIntegers E) (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by sorry
