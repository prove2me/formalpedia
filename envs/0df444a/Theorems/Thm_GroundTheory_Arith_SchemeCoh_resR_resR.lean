-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resR_resR
-- name    : GroundTheory.Arith.SchemeCoh.resR_resR
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:28:37.353087+00:00
-- url     : https://prove2.me/theorems/1f32c494-3287-4cd7-b867-97562e4fad9c
-- title:
--   Scheme Coh: res R res R
-- statement:
--   The Scheme Coh construction uses the res R res R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L143-L146

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

theorem GroundTheory.Arith.SchemeCoh.resR_resR {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (r : ringOn X U) :
    resR i (resR h r) = resR (i.trans h) r := by sorry
