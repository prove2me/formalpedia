-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_succ
-- name    : GroundTheory.Arith.SchemeCoh.inter_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:58.476137+00:00
-- url     : https://prove2.me/theorems/7579376f-15fc-46c4-ab74-6845173845bc
-- title:
--   Scheme Coh: inter succ
-- statement:
--   The Scheme Coh construction uses the inter succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean#L29-L32

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
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
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)

theorem GroundTheory.Arith.SchemeCoh.inter_succ {n : ℕ} (i : Fin (n + 2) → ι) :
    inter U i = U (i 0) ⊓ inter U (i ∘ Fin.succ) := by sorry
