-- Prove2me | Theorems.Thm_GlobalTheory_SymSignature_finrank_le
-- name    : GlobalTheory.SymSignature.finrank_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:25:28.754399+00:00
-- url     : https://prove2.me/theorems/6f30c71e-be25-4836-9636-796828272981
-- title:
--   Sym Signature: finrank le
-- statement:
--   The Sym Signature construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CardTypeLe.lean#L66-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CardTypeLe.lean#L66-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardTypeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SymSignature
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SymSignature.finrank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q g : ℕ) (K : Type) [Field K] [CharZero K] (ρ : K) (ty : Fin g → (𝓞 E →+* K)) (V : Submodule K (Matrix (Fin g) (Fin g) K)), ρ ^ 2 = -(H.d : K) → (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = q)) → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ a : 𝓞 E, Matrix.diagonal (fun i => ty i a) * Θ = Θ * (Matrix.diagonal (fun i => ty i (H.bar a))).transpose) → Module.finrank K V ≤ Module.finrank ℚ E / 2 * p * q := by sorry
