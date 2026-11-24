-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM
-- name    : GroundTheory.Arith.SchemeCoh.resM_resM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:59.900821+00:00
-- url     : https://prove2.me/theorems/d6511882-4261-4bf2-ab92-bb84165b67eb
-- title:
--   Scheme Coh: res M res M
-- statement:
--   The Scheme Coh construction uses the res M res M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L115-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L115-L118

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

theorem GroundTheory.Arith.SchemeCoh.resM_resM (P : PMod X) {U V W : X.Opens} (h : V ≤ U) (i : W ≤ V) (x : P.obj (op U)) :
    resM P i (resM P h x) = resM P (i.trans h) x := by sorry
