-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le
-- name    : GroundTheory.Arith.SchemeCoh.inter_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:06.627487+00:00
-- url     : https://prove2.me/theorems/eb3043aa-33ce-4c13-86f8-b50705ea4280
-- title:
--   Scheme Coh: inter le
-- statement:
--   The Scheme Coh construction uses the inter le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ConsCompSuccAboveZero.lean#L18-L19

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
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
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
attribute [local semireducible] inter

theorem GroundTheory.Arith.SchemeCoh.inter_le (U : ι → Opens X) {n : ℕ} (i : Fin n → ι) (a : Fin n) : inter U i ≤ U (i a) := by sorry
