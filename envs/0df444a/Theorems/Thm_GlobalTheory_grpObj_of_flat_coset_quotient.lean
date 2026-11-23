-- Prove2me | Theorems.Thm_GlobalTheory_grpObj_of_flat_coset_quotient
-- name    : GlobalTheory.grpObj_of_flat_coset_quotient
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:44.547833+00:00
-- url     : https://prove2.me/theorems/6ed7811e-5dc4-46d4-aa8f-96cd0ac53fb4
-- title:
--   Global Theory: grp Obj of flat coset quotient
-- statement:
--   The Global Theory construction uses the grp Obj of flat coset quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGroupQuotientPullback.lean#L181-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGroupQuotientPullback.lean#L181-L197

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
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.grpObj_of_flat_coset_quotient :
    ∀ (S : Scheme.{0}) (G T B : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj T] (i : T ⟶ G)
      (q : G ⟶ B), IsMonHom i → Mono i → Flat q.left → Surjective q.left →
      QuasiCompact q.left →
      (∀ (Z : Over S) (g g' : Z ⟶ G), g ≫ q = g' ≫ q ↔ ∃ t : Z ⟶ T, g' = (t ≫ i) * g) →
      ∃ (_ : GrpObj B), IsCommMonObj B ∧ IsMonHom q ∧ IsPullback i (toUnit _) q (η[B]) := by sorry
