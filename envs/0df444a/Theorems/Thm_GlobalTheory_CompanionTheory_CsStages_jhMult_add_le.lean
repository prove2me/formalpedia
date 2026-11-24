-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CsStages_jhMult_add_le
-- name    : GlobalTheory.CompanionTheory.CsStages.jhMult_add_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.686665+00:00
-- url     : https://prove2.me/theorems/d39b54a0-dcdb-4b95-ada2-cb5b464ee18d
-- title:
--   Cs Stages: jh Mult add le
-- statement:
--   The Cs Stages construction uses the jh Mult add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JhMultMulLeOfSteps.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/JhMultMulLeOfSteps.lean#L13-L19

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

theorem GlobalTheory.CompanionTheory.CsStages.jhMult_add_le {σ : Representation F G W} {ρ : Representation F G V} {ρ₁ : Representation F G V₁}
    {ρ₂ : Representation F G V₂} (ι : ρ₁.IntertwiningMap ρ) (p : ρ.IntertwiningMap ρ₂)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (h0 : ∀ u, p (ι u) = 0) :
    jhMult σ ρ₁ + jhMult σ ρ₂ ≤ jhMult σ ρ := by sorry
