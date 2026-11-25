-- Prove2me | Theorems.Thm_GlobalTheory_Ker_CreOp_foldr_creation_zero
-- name    : GlobalTheory.Ker.CreOp.foldr_creation_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:12:09.118806+00:00
-- url     : https://prove2.me/theorems/9f4fcb98-4c12-4de3-8b7c-8a4ee76aaa24
-- title:
--   Cre Op: foldr creation zero
-- statement:
--   The Cre Op construction uses the foldr creation zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L112-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FoldrHolDEqIteratedFDeriv.lean#L112-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FoldrHolDEqIteratedFDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.Ker GlobalTheory.Ker.CreOp
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable {σ : Type} (u : σ → W)

theorem GlobalTheory.Ker.CreOp.foldr_creation_zero : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by sorry
