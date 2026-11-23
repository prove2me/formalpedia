-- Prove2me | Theorems.Thm_GlobalTheory_SplitTorusHom_appTop_id
-- name    : GlobalTheory.SplitTorusHom.appTop_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:18.542043+00:00
-- url     : https://prove2.me/theorems/de01c0f0-7a9c-4a98-921c-30de12da9f2b
-- title:
--   Split Torus Hom: app Top id
-- statement:
--   The Split Torus Hom construction uses the app Top id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsAddEquivOfSplitTorusIso.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsAddEquivOfSplitTorusIso.lean#L22-L24

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

theorem GlobalTheory.SplitTorusHom.appTop_id {A : Over S} (r : Γ(A.left, ⊤)) : (𝟙 A : A ⟶ A).left.appTop.hom r = r := by sorry
