-- Prove2me | Theorems.Thm_GlobalTheory_CosetQuotient_flat_tensorHom
-- name    : GlobalTheory.CosetQuotient.flat_tensorHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:37.518743+00:00
-- url     : https://prove2.me/theorems/e48538dd-3326-49c7-a256-f5197a969129
-- title:
--   Coset Quotient: flat tensor Hom
-- statement:
--   The Coset Quotient construction uses the flat tensor Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGroupQuotientPullback.lean#L161-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGroupQuotientPullback.lean#L161-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGroupQuotientPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory
open GlobalTheory.CosetQuotient
universe v u
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}

theorem GlobalTheory.CosetQuotient.flat_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hg : Flat g.left] : Flat (f ⊗ₘ g).left := by sorry
