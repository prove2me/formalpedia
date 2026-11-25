-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_dualEval
-- name    : GroundTheory.Arith.SchemeCoh.isIso_dualEval
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:10.30583+00:00
-- url     : https://prove2.me/theorems/1cf656c8-f825-4132-9d08-c9d61801f869
-- title:
--   Scheme Coh: is Iso dual Eval
-- statement:
--   The Scheme Coh construction uses the is Iso dual Eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L348-L365
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L348-L365

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

theorem GroundTheory.Arith.SchemeCoh.isIso_dualEval {M : X.Modules} (hM : IsInvertibleSheaf M) : IsIso (dualEval M) := by sorry
