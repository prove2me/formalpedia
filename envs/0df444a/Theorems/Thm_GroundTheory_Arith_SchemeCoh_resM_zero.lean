-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_zero
-- name    : GroundTheory.Arith.SchemeCoh.resM_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:48.028069+00:00
-- url     : https://prove2.me/theorems/a5a7fdda-b744-4f2d-b23b-b389d40f5e69
-- title:
--   Scheme Coh: res M zero
-- statement:
--   The Scheme Coh construction uses the res M zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L128-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L128-L129

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

theorem GroundTheory.Arith.SchemeCoh.resM_zero (P : PMod X) {U V : X.Opens} (h : V ≤ U) : resM P h (0 : P.obj (op U)) = 0 := by sorry
