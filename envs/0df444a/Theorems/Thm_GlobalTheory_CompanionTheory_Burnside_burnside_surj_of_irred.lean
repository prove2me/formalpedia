-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Burnside_burnside_surj_of_irred
-- name    : GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:27:07.057974+00:00
-- url     : https://prove2.me/theorems/4c6ab769-b78e-4534-921f-e4b744d6b73c
-- title:
--   Burnside: burnside surj of irred
-- statement:
--   The Burnside construction uses the burnside surj of irred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BurnsideSurjOfIrred.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BurnsideSurjOfIrred.lean#L18-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemOfIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BurnsideSurjOfIrred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Burnside

theorem GlobalTheory.CompanionTheory.Burnside.burnside_surj_of_irred {A V : Type} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : A →ₐ[ℂ] Module.End ℂ V) (hirr : ∀ W : Submodule ℂ V, (∀ h, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Function.Surjective ρ := by sorry
