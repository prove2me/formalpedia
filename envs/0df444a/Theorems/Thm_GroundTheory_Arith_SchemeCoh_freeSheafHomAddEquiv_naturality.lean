-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeSheafHomAddEquiv_naturality
-- name    : GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:58:42.1558+00:00
-- url     : https://prove2.me/theorems/9a236c8a-3788-4286-bef0-2bf5c671959c
-- title:
--   Scheme Coh: free Sheaf Hom Add Equiv naturality
-- statement:
--   The Scheme Coh construction uses the free Sheaf Hom Add Equiv naturality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L100-L105

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Limits Opposite Abelian
universe w' v u
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{v}]

theorem GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{v}}
    (g : freeSheaf J U ⟶ F) (φ : F ⟶ G) :
    freeSheafHomAddEquiv U G (g ≫ φ) = φ.hom.app (op U) (freeSheafHomAddEquiv U F g) := by sorry
