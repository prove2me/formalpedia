-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechOrdered_homotopy_apply
-- name    : GroundTheory.Arith.SchemeCoh.CechOrdered.homotopy_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:03:30.395853+00:00
-- url     : https://prove2.me/theorems/80b46d5e-64fd-4af8-9772-1fef5a396c89
-- title:
--   Cech Ordered: homotopy apply
-- statement:
--   The Cech Ordered construction uses the homotopy apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L535-L536
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechOrdered.lean#L535-L536

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

theorem GroundTheory.Arith.SchemeCoh.CechOrdered.homotopy_apply (q : ℕ) (σ : Cochain P U (q + 1)) (i : Fin (q + 1) → ι) :
    homotopy P U q σ i = pair σ (inter U i) (hom q i) := by sorry
