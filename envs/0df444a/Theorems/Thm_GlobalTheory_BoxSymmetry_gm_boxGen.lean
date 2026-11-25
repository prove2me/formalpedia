-- Prove2me | Theorems.Thm_GlobalTheory_BoxSymmetry_gm_boxGen
-- name    : GlobalTheory.BoxSymmetry.gm_boxGen
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:48.349089+00:00
-- url     : https://prove2.me/theorems/56b3fcf7-b619-446c-bd04-a923a379e6e4
-- title:
--   Box Symmetry: gm box Gen
-- statement:
--   The Box Symmetry construction uses the gm box Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BoxSymIsSymmetry.lean#L35-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BoxSymIsSymmetry.lean#L35-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_SubAddEqZeroOfEqAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BoxSymIsSymmetry
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
open GlobalTheory GlobalTheory.BoxSymmetry
variable {X X' Y Z : Scheme.{0}} (L : LB X) {J K : Type} [Fintype J] [Fintype K]

theorem GlobalTheory.BoxSymmetry.gm_boxGen (F : J → (X' ⟶ X)) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : ∀ i, LB.Gen (LB.LinComb (L.pull (F i)) φ ε)) (r : Z ⟶ Y) (z : Z)
    (jj : K → (LB.LinComb L F (fun _ => 1)).ι)
    (h : r z ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) :
    gm r z (LB.wchart (LB.LinComb L F (fun _ => 1)) φ jj) ((GeneratorPullback.boxGen L F φ ε t).s jj) =
      ∏ i, gm r z (LB.wchart (L.pull (F i)) φ (fun k _ => jj k i)) ((t i).s (fun k _ => jj k i)) := by sorry
