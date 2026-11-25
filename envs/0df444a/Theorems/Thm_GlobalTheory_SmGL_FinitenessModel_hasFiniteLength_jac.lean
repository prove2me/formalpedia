-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_hasFiniteLength_jac
-- name    : GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_jac
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:44.829798+00:00
-- url     : https://prove2.me/theorems/612f4145-87a4-5093-97dd-86bfa791ac79
-- title:
--   Finiteness Model: has Finite Length jac
-- statement:
--   The Finiteness Model construction uses the has Finite Length jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L46-L48

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

theorem GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_jac (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ (GL n k) V) : HasFiniteLength (jac e π) := by sorry
