-- Prove2me | Theorems.Thm_GlobalTheory_ToSplit_IsFrame_trans_id
-- name    : GlobalTheory.ToSplit.IsFrame.trans_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:26.457991+00:00
-- url     : https://prove2.me/theorems/364d9f5b-adcd-4d66-92bd-157f65968ed5
-- title:
--   Is Frame: trans id
-- statement:
--   The Is Frame construction uses the trans id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L354-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSplitExtDatumOfSplitTorusExtension.lean#L354-L358

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
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
omit [IsMonHom q] [IsMonHom i] [Flat q.left] [Surjective q.left] [QuasiCompact q.left]

theorem GlobalTheory.ToSplit.IsFrame.trans_id {χ : X} {O : RigLB B} {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ}
    (h : IsFrame q i χ O u) (j j' : O.L.ι) (y : G.left) (h₁ : q.left y ∈ O.L.U j)
    (h₂ : q.left y ∈ O.L.U j') : gm q.left y (O.L.U j ⊓ O.L.U j') (O.L.g j j') =
      gm (𝟙 _) y _ (u j') / gm (𝟙 _) y _ (u j) := by sorry
