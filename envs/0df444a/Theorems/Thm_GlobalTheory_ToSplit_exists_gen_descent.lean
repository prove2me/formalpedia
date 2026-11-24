-- Prove2me | Theorems.Thm_GlobalTheory_ToSplit_exists_gen_descent
-- name    : GlobalTheory.ToSplit.exists_gen_descent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:50.361051+00:00
-- url     : https://prove2.me/theorems/61d3a6a6-1a2d-4692-8b2c-b2e92246dbdd
-- title:
--   To Split: exists gen descent
-- statement:
--   The To Split construction uses the exists gen descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L80-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L80-L91

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X Y : Over S} (π : Y ⟶ X) [Flat π.left] [Surjective π.left]
  [QuasiCompact π.left]

theorem GlobalTheory.ToSplit.exists_gen_descent (M : LB X.left) (f : ∀ j, Γ(Y.left, π.left ⁻¹ᵁ M.U j)ˣ)
    (hf : ∀ j (Z : Over S) (g₁ g₂ : Z ⟶ Y) (z : Z.left), g₁ ≫ π = g₂ ≫ π →
      π.left (g₁.left z) ∈ M.U j → π.left (g₂.left z) ∈ M.U j →
      gm g₁.left z _ (f j) = gm g₂.left z _ (f j))
    (hg : ∀ j j' (y : Y.left), π.left y ∈ M.U j → π.left y ∈ M.U j' →
      gm (𝟙 _) y _ (f j) = gm π.left y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 _) y _ (f j')) :
    ∃ t : LB.Gen M, t.IsGen := by sorry
