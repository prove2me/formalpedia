-- Prove2me | Theorems.Thm_GlobalTheory_T_siegelWeilDifference_automorphy_linearity
-- name    : GlobalTheory.T.siegelWeilDifference_automorphy_linearity
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:30:57.819746+00:00
-- url     : https://prove2.me/theorems/8f3a2d1b-8471-4d2f-86bb-64b1d34220df
-- title:
--   T: siegel Weil Difference automorphy linearity
-- statement:
--   The T construction uses the siegel Weil Difference automorphy linearity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearityStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearityStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.siegelWeilDifference_automorphy_linearity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M : ℕ) (φ : Fam E n N), 0 < M → (∀ Λ ∈ Vset E n M, IsSB (φ Λ)) → ∀ Z ∈ Hn Ψ N, (∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0) ∧ (∀ β : Matrix (Fin N) (Fin N) E, ccT β = β → swd Ψ M (fun Λ x => chiH Ψ β x * φ Λ x) Z 0 0 = swd Ψ M φ (fun τ => Z τ + β.map τ.1) 0 0) ∧ (∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → swd Ψ M (φ + ψ) Z 0 0 = swd Ψ M φ Z 0 0 + swd Ψ M ψ Z 0 0) ∧ (∀ c : ℂ, swd Ψ M (c • φ) Z 0 0 = c * swd Ψ M φ Z 0 0) ∧ ∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) → swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := by sorry
