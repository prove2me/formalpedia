-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_apply_of_not_injective
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_not_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:00.591955+00:00
-- url     : https://prove2.me/theorems/10cca03c-f958-4072-a90c-9315827902d2
-- title:
--   Cech Ordered: alt Proj apply of not injective
-- statement:
--   The Cech Ordered construction uses the alt Proj apply of not injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L542-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L542-L544

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered
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
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable {ι : Type w} [LinearOrder ι] {X : TopCat.{u}} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (U : ι → Opens X)
variable {P U}

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_not_injective (q : ℕ) (σ : Cochain P U q) {i : Fin (q + 1) → ι}
    (hi : ¬ Function.Injective i) : altProj P U q σ i = 0 := by sorry
