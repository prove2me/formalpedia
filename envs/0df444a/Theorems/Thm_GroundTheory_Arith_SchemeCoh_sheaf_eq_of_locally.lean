-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_eq_of_locally
-- name    : GroundTheory.Arith.SchemeCoh.sheaf_eq_of_locally
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:07.33251+00:00
-- url     : https://prove2.me/theorems/25cc9ad0-ab6f-41bc-9f69-a7ded2d7bb54
-- title:
--   Scheme Coh: sheaf eq of locally
-- statement:
--   The Scheme Coh construction uses the sheaf eq of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L81-L92

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}

theorem GroundTheory.Arith.SchemeCoh.sheaf_eq_of_locally {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} (s t : ToType (F.1.obj (op V)))
    (h : ∀ x ∈ V, ∃ (W : Opens T) (i : W ≤ V), x ∈ W ∧
      F.1.map (homOfLE i).op s = F.1.map (homOfLE i).op t) : s = t := by sorry
