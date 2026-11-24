-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Herm_exists_eigen
-- name    : GlobalTheory.ThK.Dbl.Herm.exists_eigen
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:25.044959+00:00
-- url     : https://prove2.me/theorems/55cebfc1-eebb-47f6-abb1-500d8c944172
-- title:
--   Herm: exists eigen
-- statement:
--   The Herm construction uses the exists eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HermAbs.lean#L28-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/HermAbs.lean#L28-L76

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_HermAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Herm
open scoped InnerProductSpace
open PositivityTheory.ThKF.Abs
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem GlobalTheory.ThK.Dbl.Herm.exists_eigen {K : Type} [Group K] (κ : K →* Module.End ℂ U) (hi : ∀ k x y, ⟪κ k x, κ k y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hf : ∀ x, FiniteDimensional ℂ (orb κ x)) {ι : Type} [Finite ι] (l : ι → U →ₗ[ℂ] ℂ)
    (hl : ∀ x, (∀ i k, l i (κ k x) = 0) → x = 0) (b : U →ₗ⋆[ℂ] U →ₗ[ℂ] ℂ) (hb : ∀ k x y, b (κ k x) (κ k y) = b x y)
    (f : U) (h0 : f ≠ 0) : ∃ (x : U) (c : ℂ), x ≠ 0 ∧ ∀ y, b x y = c * ⟪x, y⟫_ℂ := by sorry
