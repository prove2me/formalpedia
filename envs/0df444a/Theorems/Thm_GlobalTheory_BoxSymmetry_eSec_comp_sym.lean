-- Prove2me | Theorems.Thm_GlobalTheory_BoxSymmetry_eSec_comp_sym
-- name    : GlobalTheory.BoxSymmetry.eSec_comp_sym
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:09.548828+00:00
-- url     : https://prove2.me/theorems/8f421b50-1179-5b29-bfe5-3f0177b5a757
-- title:
--   Box Symmetry: e Sec comp sym
-- statement:
--   The Box Symmetry construction uses the e Sec comp sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BoxSymIsSymmetry.lean#L165-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BoxSymIsSymmetry.lean#L165-L168

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
variable {S : Scheme.{0}}

theorem GlobalTheory.BoxSymmetry.eSec_comp_sym (H : Over S) [GrpObj H] (k : Fin 2) :
    eSec H ≫ (![(ι[H]).left, 𝟙 H.left] : Fin 2 → (H.left ⟶ H.left)) k = eSec H := by sorry
