-- Prove2me | Theorems.Thm_GlobalTheory_GeneratorLaw_compat_iff
-- name    : GlobalTheory.GeneratorLaw.compat_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:42:12.889444+00:00
-- url     : https://prove2.me/theorems/6c9001d2-acef-4602-903f-3d9d2d03c62e
-- title:
--   Generator Law: compat iff
-- statement:
--   The Generator Law construction uses the compat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGrpObjSplitExtensionOfGenerators.lean#L144-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGrpObjSplitExtensionOfGenerators.lean#L144-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GeneratorSchemeProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGrpObjSplitExtensionOfGenerators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GeneratorLaw
variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem GlobalTheory.GeneratorLaw.compat_iff {b : Y ⟶ X} (s : ∀ i : L.ι, Γ(Y, b ⁻¹ᵁ L.U i)ˣ) : GenScheme.Compat L b s ↔
    ∀ Z (r : Z ⟶ Y) (z : Z) i i', b (r z) ∈ L.U i → b (r z) ∈ L.U i' → gm r z (b ⁻¹ᵁ L.U i') (s i') =
      gm (r ≫ b) z _ (L.g i i') * gm r z (b ⁻¹ᵁ L.U i) (s i) := by sorry
