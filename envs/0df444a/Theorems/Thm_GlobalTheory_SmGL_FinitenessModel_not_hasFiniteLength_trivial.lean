-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_not_hasFiniteLength_trivial
-- name    : GlobalTheory.SmGL.FinitenessModel.not_hasFiniteLength_trivial
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:24:30.799223+00:00
-- url     : https://prove2.me/theorems/81bc6527-0284-4d6b-8d0c-c0c30b1fadf2
-- title:
--   Finiteness Model: not has Finite Length trivial
-- statement:
--   The Finiteness Model construction uses the not has Finite Length trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L50-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.FinitenessModel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.FinitenessModel.not_hasFiniteLength_trivial :
    IsSmooth (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) ∧
      ¬ HasFiniteLength (Representation.trivial ℂ (GL n k) (ℕ →₀ ℂ)) := by sorry
