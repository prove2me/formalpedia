-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_refl
-- name    : GroundTheory.Arith.SchemeCoh.resM_refl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:25.883495+00:00
-- url     : https://prove2.me/theorems/7d578327-994c-4b38-9225-c1f7f10da6ff
-- title:
--   Scheme Coh: res M refl
-- statement:
--   The Scheme Coh construction uses the res M refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L270-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L270-L273

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
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

theorem GroundTheory.Arith.SchemeCoh.resM_refl (P : PMod X) {U : X.Opens} (x : P.obj (op U)) : resM P (le_refl U) x = x := by sorry
