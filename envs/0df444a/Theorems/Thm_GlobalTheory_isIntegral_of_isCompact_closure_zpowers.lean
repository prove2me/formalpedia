-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_isCompact_closure_zpowers
-- name    : GlobalTheory.isIntegral_of_isCompact_closure_zpowers
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:26.177263+00:00
-- url     : https://prove2.me/theorems/5e649c75-4033-4c0c-914b-de22683a0f2a
-- title:
--   Global Theory: is Integral of is Compact closure zpowers
-- statement:
--   The Global Theory construction uses the is Integral of is Compact closure zpowers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowers.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsIntegralOfIsCompactClosureZpowers.lean#L77-L83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralOfIsCompactClosureZpowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory
open NumberField IsDedekindDomain

theorem GlobalTheory.isIntegral_of_isCompact_closure_zpowers (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (g : GL (Fin n) (w.adicCompletion E))
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) (w.adicCompletion E))))) :
    IsIntegral (w.adicCompletionIntegers E)
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by sorry
