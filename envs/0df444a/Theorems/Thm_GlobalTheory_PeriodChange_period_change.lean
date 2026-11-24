-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChange_period_change
-- name    : GlobalTheory.PeriodChange.period_change
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:39.432179+00:00
-- url     : https://prove2.me/theorems/f409f597-7f96-4fdf-bb6c-d551aebdac92
-- title:
--   Period Change: period change
-- statement:
--   The Period Change construction uses the period change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L96-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ChangeOfNormalisation.lean#L96-L172

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ChangeOfNormalisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChange
open Complex Matrix NumberField

theorem GlobalTheory.PeriodChange.period_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (P P' : D.La →+ (Fin g → ℂ)) (h h' τ τ' : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.omegaStd a b) → (∀ a b, D.EF (gam a) (gam b) = D.EF a b) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ a, P' a = P (gam a)) → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → (∀ k, h' *ᵥ P' (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h' *ᵥ P' (bas (Pi.single (Sum.inr k) 1)) = τ' *ᵥ Pi.single k 1) → τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → τ' ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g) → IsUnit h.det → ∃ γ ∈ Matrix.symplecticGroup (Fin g) ℤ, γ = Matrix.fromBlocks N.toBlocks₂₂ᵀ N.toBlocks₁₂ᵀ N.toBlocks₂₁ᵀ N.toBlocks₁₁ᵀ ∧ τ' = _root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.spAct γ τ ∧ h' = ((_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ)⁻¹)ᵀ * h ∧ h.det = (_root_.ReciprocityTheory.ChartRestriction.G.Key.Chi.jAut γ τ).det * h'.det := by sorry
