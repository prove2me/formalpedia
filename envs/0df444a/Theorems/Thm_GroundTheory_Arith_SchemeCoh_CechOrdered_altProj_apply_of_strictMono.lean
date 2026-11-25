-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_altProj_apply_of_strictMono
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_strictMono
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:26:31.58501+00:00
-- url     : https://prove2.me/theorems/fe522866-d4b7-408d-acdc-8bb9a7d8bc00
-- title:
--   Cech Ordered: alt Proj apply of strict Mono
-- statement:
--   The Cech Ordered construction uses the alt Proj apply of strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L538-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L538-L540

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

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.altProj_apply_of_strictMono (q : ℕ) (σ : Cochain P U q) {i : Fin (q + 1) → ι}
    (hi : StrictMono i) : altProj P U q σ i = σ i := by sorry
