-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsInvertibleSheaf_dual
-- name    : GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.dual
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:01.625129+00:00
-- url     : https://prove2.me/theorems/c7156d49-e886-4194-b1fc-a140ba289711
-- title:
--   Is Invertible Sheaf: dual
-- statement:
--   The Is Invertible Sheaf construction uses the dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L341-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleDual.lean#L341-L346

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

theorem GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.dual {M : X.Modules} (hM : IsInvertibleSheaf M) :
    IsInvertibleSheaf (dualSheaf M) := by sorry
