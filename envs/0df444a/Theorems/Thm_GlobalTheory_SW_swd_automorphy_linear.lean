-- Prove2me | Theorems.Thm_GlobalTheory_SW_swd_automorphy_linear
-- name    : GlobalTheory.SW.swd_automorphy_linear
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:56:42.255905+00:00
-- url     : https://prove2.me/theorems/d9591263-4383-4374-bdef-fa62be9dbd31
-- title:
--   SW: swd automorphy linear
-- statement:
--   The SW construction uses the swd automorphy linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearity.lean#L55-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelWeilDifferenceAutomorphyLinearity.lean#L55-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EisAutomorphyLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionSiegelParabolicExplicitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelWeilDifferenceAutomorphyLinearity
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
open GlobalTheory.SW.SwdAut

theorem GlobalTheory.SW.swd_automorphy_linear : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → 4 * N < n → ∀ (M : ℕ) (φ : Fam E n N), 0 < M → (∀ Λ ∈ Vset E n M, IsSB (φ Λ)) → ∀ Z ∈ Hn Ψ N, (∀ γ ∈ UU E N, swd Ψ M (fun Λ => weil Ψ γ (φ Λ)) (hAct Ψ γ Z) 0 0 = hFac Ψ γ Z (0 : CM Ψ n N) 0 * swd Ψ M φ Z 0 0) ∧ (∀ β : Matrix (Fin N) (Fin N) E, ccT β = β → swd Ψ M (fun Λ x => chiH Ψ β x * φ Λ x) Z 0 0 = swd Ψ M φ (fun τ => Z τ + β.map τ.1) 0 0) ∧ (∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, IsSB (ψ Λ)) → swd Ψ M (φ + ψ) Z 0 0 = swd Ψ M φ Z 0 0 + swd Ψ M ψ Z 0 0) ∧ (∀ c : ℂ, swd Ψ M (c • φ) Z 0 0 = c * swd Ψ M φ Z 0 0) ∧ ∀ ψ : Fam E n N, (∀ Λ ∈ Vset E n M, ψ Λ = φ Λ) → swd Ψ M ψ Z 0 0 = swd Ψ M φ Z 0 0 := by sorry
