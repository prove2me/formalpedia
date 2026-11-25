-- Prove2me | Theorems.Thm_GlobalTheory_KS_exists_isSymm_of_square
-- name    : GlobalTheory.KS.exists_isSymm_of_square
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:57:45.008542+00:00
-- url     : https://prove2.me/theorems/954847e3-7155-47d7-b1cc-7eaf2808ff74
-- title:
--   KS: exists is Symm of square
-- statement:
--   The KS construction uses the exists is Symm of square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L156-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsSymmOfSquare.lean#L156-L198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KunnethSymmProductAffineCoversStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsSymmOfSquare
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS
open Square

theorem GlobalTheory.KS.exists_isSymm_of_square : ∀ (K : Type) [Field K] (Y Z : Scheme.{0}) (q : Y ⟶ Sp K) (p₁ p₂ : Z ⟶ Y) (I : Type) [Finite I] (U : I → Y.Opens) (g : ℕ) (θ φ : Fin g → C1 U), IsSeparated q → IsPullback p₁ p₂ q q → (∀ i, IsAffineOpen (U i)) → (∀ c, IsCob U (lc q c φ) → c = 0) → ∀ (J : Type) (V : J → Z.Opens) (k : ∀ i j, C1 (fun α => p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ U j ⊓ V α)) (e : Fin g → ∀ j α, Γ(Z, p₂ ⁻¹ᵁ U j ⊓ V α)) (e' : Fin g → ∀ i α, Γ(Z, p₁ ⁻¹ᵁ U i ⊓ V α)), ⨆ α, V α = ⊤ → (∀ i j, IsCoc _ (k i j)) → (∀ a j j' α O, O ≤ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α → rsT (e a j' α) O - rsT (e a j α) O = pbT p₂ (φ a j j') O) → (∀ a i i' α O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ V α → rsT (e' a i' α) O - rsT (e' a i α) O = pbT p₁ (φ a i i') O) → (∀ i i' j α β O, O ≤ p₁ ⁻¹ᵁ (U i ⊓ U i') ⊓ p₂ ⁻¹ᵁ U j ⊓ V α ⊓ V β → rsT (k i' j α β) O - rsT (k i j α β) O = ∑ a, pbT p₁ (θ a i i') O * (rsT (e a j α) O - rsT (e a j β) O)) → (∀ i j j' α β O, O ≤ p₁ ⁻¹ᵁ U i ⊓ p₂ ⁻¹ᵁ (U j ⊓ U j') ⊓ V α ⊓ V β → rsT (k i j' α β) O - rsT (k i j α β) O = ∑ a, pbT p₂ (θ a j j') O * (rsT (e' a i α) O - rsT (e' a i β) O)) → ∃ Θ : Matrix (Fin g) (Fin g) K, Θ.IsSymm ∧ ∀ b, IsCob U (θ b - lc q (Θ b) φ) := by sorry
