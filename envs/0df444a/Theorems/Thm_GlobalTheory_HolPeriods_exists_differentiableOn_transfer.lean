-- Prove2me | Theorems.Thm_GlobalTheory_HolPeriods_exists_differentiableOn_transfer
-- name    : GlobalTheory.HolPeriods.exists_differentiableOn_transfer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:02.029207+00:00
-- url     : https://prove2.me/theorems/ceb7c9b2-92a2-44be-b6b4-043c74bd3a70
-- title:
--   Hol Periods: exists differentiable On transfer
-- statement:
--   The Hol Periods construction uses the exists differentiable On transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L75-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsDifferentiableOnTransfer.lean#L75-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolPeriods

theorem GlobalTheory.HolPeriods.exists_differentiableOn_transfer {V Λ : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [AddCommGroup Λ]
    {g : ℕ} {B : Set V} (hB : IsOpen B) {Q Q' : V → (Λ →+ (Fin g → ℂ))}
    (hQ : ∀ x, DifferentiableOn ℂ (fun b => Q b x) B) (hQ' : ∀ x, DifferentiableOn ℂ (fun b => Q' b x) B)
    {b₀ : V} (hb₀ : b₀ ∈ B) (hspan : Submodule.span ℝ (Set.range (Q b₀)) = ⊤)
    (k : V → ((Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) (hk : ∀ b ∈ B, ∀ x, Q' b x = k b (Q b x)) :
    ∃ B' : Set V, IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧
      DifferentiableOn ℂ (fun bz : V × (Fin g → ℂ) => k bz.1 bz.2) (B' ×ˢ Set.univ) := by sorry
