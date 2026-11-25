-- Prove2me | Theorems.Thm_GlobalTheory_TorusCube_unit_eq_one
-- name    : GlobalTheory.TorusCube.unit_eq_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:31.428176+00:00
-- url     : https://prove2.me/theorems/189e43ac-e242-4449-94c7-08ffc46e50c6
-- title:
--   Torus Cube: unit eq one
-- statement:
--   The Torus Cube construction uses the unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SplitTorusGenCubical.lean#L79-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SplitTorusGenCubical.lean#L79-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
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
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor

theorem GlobalTheory.TorusCube.unit_eq_one (k : Type) [Field k] (X : Type) [AddCommGroup X] [TwoUniqueSums (X × X × X)]
    (w : Γ((splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗
      splitTorus (Spec (.of k)) X).left, ⊤)) (hw : IsUnit w)
    (h₀ : (lift (𝟙 _) (lift 1 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₁ : (lift 1 (lift (𝟙 _) 1) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (h₂ : (lift 1 (lift 1 (𝟙 _)) : splitTorus (Spec (.of k)) X ⟶
      splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X ⊗ splitTorus (Spec (.of k)) X).left.appTop.hom w = 1)
    (Z : Over (Spec (.of k))) (x y u : Z ⟶ splitTorus (Spec (.of k)) X) :
    (lift x (lift y u)).left.appTop.hom w = 1 := by sorry
