-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul
-- name    : GroundTheory.Arith.SchemeCoh.resM_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:28.376595+00:00
-- url     : https://prove2.me/theorems/0f9b037c-f0e0-4fa2-90ee-20a0e35795a9
-- title:
--   Scheme Coh: res M smul
-- statement:
--   The Scheme Coh construction uses the res M smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L120-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L120-L122

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

theorem GroundTheory.Arith.SchemeCoh.resM_smul (P : PMod X) {U V : X.Opens} (h : V ≤ U) (r : ringOn X U) (x : P.obj (op U)) :
    resM P h (r • x) = resR h r • resM P h x := by sorry
