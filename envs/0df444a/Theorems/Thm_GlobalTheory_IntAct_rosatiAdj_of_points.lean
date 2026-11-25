-- Prove2me | Theorems.Thm_GlobalTheory_IntAct_rosatiAdj_of_points
-- name    : GlobalTheory.IntAct.rosatiAdj_of_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:34.325465+00:00
-- url     : https://prove2.me/theorems/6da10f9d-a241-4c76-99eb-089987a3449c
-- title:
--   Int Act: rosati Adj of points
-- statement:
--   The Int Act construction uses the rosati Adj of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L21-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem GlobalTheory.IntAct.rosatiAdj_of_points (hL : L.IsLB) (f g : A ⟶ A)
    (h : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∀ (T : Over S) (x y : T ⟶ A), (∀ p, T.hom p ∈ U) →
      ∃ (K : Type) (_ : Fintype K) (φ : K → (T.left ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
        t.IsGen ∧ ∀ (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V), ∏ i, k (φ i) ^ ε i =
          k ((x ≫ f) * y).left * (k (x ≫ f).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ g)).left)⁻¹ * k x.left *
            k (y ≫ g).left) : RosatiAdj A L f g := by sorry
