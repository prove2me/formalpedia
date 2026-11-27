-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_freeSheafHomAddEquiv_naturality_left
-- name    : GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:48.068013+00:00
-- url     : https://prove2.me/theorems/870f3c70-4f28-4898-af0e-0e2ad0de3746
-- title:
--   Scheme Coh: free Sheaf Hom Add Equiv naturality left
-- statement:
--   The Scheme Coh construction uses the free Sheaf Hom Add Equiv naturality left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/SheafH.lean#L107-L113

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

theorem GroundTheory.Arith.SchemeCoh.freeSheafHomAddEquiv_naturality_left {U V : C} (f : U ⟶ V) (F : Sheaf J AddCommGrpCat.{v})
    (g : freeSheaf J V ⟶ F) :
    freeSheafHomAddEquiv U F (freeSheafMap J f ≫ g) =
      F.obj.map f.op (freeSheafHomAddEquiv V F g) := by sorry
