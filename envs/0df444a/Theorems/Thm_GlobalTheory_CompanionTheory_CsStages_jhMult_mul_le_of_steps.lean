-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CsStages_jhMult_mul_le_of_steps
-- name    : GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:51.305311+00:00
-- url     : https://prove2.me/theorems/f4783baf-0651-4fb7-8b6c-0139f1c87f8f
-- title:
--   Cs Stages: jh Mult mul le of steps
-- statement:
--   The Cs Stages construction uses the jh Mult mul le of steps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JhMultMulLeOfSteps.lean#L21-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JhMultMulLeOfSteps.lean#L21-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JhMultMulLeOfSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JHMult
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CsStages
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

theorem GlobalTheory.CompanionTheory.CsStages.jhMult_mul_le_of_steps (σ : Representation F G W) (ρ : Representation F G V)
    (A : Subrepresentation ρ → ℕ∞) (m : ℕ∞) (hmono : ∀ S T : Subrepresentation ρ, T ≤ S → A T ≤ A S)
    (hstep : ∀ S T : Subrepresentation ρ, T ≤ S → Nonempty ((subQuot S T).Equiv σ) → A T + m ≤ A S) :
    jhMult σ ρ * m ≤ A ⊤ := by sorry
