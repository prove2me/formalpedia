-- Prove2me | Theorems.Thm_GlobalTheory_flatQuotient_iso_of_same_kernel
-- name    : GlobalTheory.flatQuotient_iso_of_same_kernel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:24.171718+00:00
-- url     : https://prove2.me/theorems/f5c1efa0-9a18-4e98-af62-69e1999d4bb6
-- title:
--   Global Theory: flat Quotient iso of same kernel
-- statement:
--   The Global Theory construction uses the flat Quotient iso of same kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L143-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L143-L160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.flatQuotient_iso_of_same_kernel :
    ∀ (S : Scheme.{0}) (G B B' T T' : Over S) [GrpObj G] [GrpObj B] [GrpObj B'] [GrpObj T]
      [GrpObj T'] (q : G ⟶ B) (i : T ⟶ G) (q' : G ⟶ B') (i' : T' ⟶ G),
      IsMonHom q → IsMonHom i → Flat q.left → Surjective q.left → QuasiCompact q.left →
      IsPullback i (toUnit _) q (η[B]) → IsMonHom q' → IsMonHom i' → Flat q'.left →
      Surjective q'.left → QuasiCompact q'.left → IsPullback i' (toUnit _) q' (η[B']) →
      i' ≫ q = toUnit _ ≫ η[B] → i ≫ q' = toUnit _ ≫ η[B'] →
      ∃ β : B' ≅ B, IsMonHom β.hom ∧ q' ≫ β.hom = q := by sorry
