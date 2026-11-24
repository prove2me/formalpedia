-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_exists_glue
-- name    : GroundTheory.Arith.SchemeCoh.sheaf_exists_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:24.755865+00:00
-- url     : https://prove2.me/theorems/1f19c0b9-b93e-4d6b-95c2-dd8f434560ad
-- title:
--   Scheme Coh: sheaf exists glue
-- statement:
--   The Scheme Coh construction uses the sheaf exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L94-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L94-L105

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

theorem GroundTheory.Arith.SchemeCoh.sheaf_exists_glue {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type u}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{u} C FC]
    [Limits.HasLimitsOfSize.{u, u} C] [(forget C).ReflectsIsomorphisms]
    [Limits.PreservesLimitsOfSize.{u, u} (forget C)]
    {T : TopCat.{u}} (F : TopCat.Sheaf C T) {V : Opens T} {ι : Type u} (W : ι → Opens T)
    (i : ∀ a, W a ≤ V) (hcov : ∀ x ∈ V, ∃ a, x ∈ W a) (sf : ∀ a, ToType (F.1.obj (op (W a))))
    (hsf : ∀ a b, F.1.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op (sf a) =
      F.1.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op (sf b)) :
    ∃ s : ToType (F.1.obj (op V)), ∀ a, F.1.map (homOfLE (i a)).op s = sf a := by sorry
