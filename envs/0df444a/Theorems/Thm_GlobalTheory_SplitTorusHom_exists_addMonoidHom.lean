-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorusHom_exists_addMonoidHom
-- name    : GlobalTheory.SplitTorusHom.exists_addMonoidHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:29.143073+00:00
-- url     : https://prove2.me/theorems/5330ec10-da4f-44d0-bcf4-e1fad6e730ab
-- title:
--   Split Torus Hom: exists add Monoid Hom
-- statement:
--   The Split Torus Hom construction uses the exists add Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsAddEquivOfSplitTorusIso.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsAddEquivOfSplitTorusIso.lean#L61-L66

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsAddEquivOfSplitTorusIso
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
open GlobalTheory.SplitTorusHom
variable {S : Scheme.{0}}
variable {X X' : Type} [AddCommGroup X] [AddCommGroup X']

theorem GlobalTheory.SplitTorusHom.exists_addMonoidHom [ConnectedSpace S]
    (f : splitTorus S X' ⟶ splitTorus S X) [IsMonHom f] :
    ∃ φ : X →+ X', ∀ χ, f.left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by sorry
