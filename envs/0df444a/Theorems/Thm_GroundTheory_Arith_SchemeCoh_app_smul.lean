-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_smul
-- name    : GroundTheory.Arith.SchemeCoh.app_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:48.889452+00:00
-- url     : https://prove2.me/theorems/c3e385fb-38c6-4758-b27b-7a1f2298d2d4
-- title:
--   Scheme Coh: app smul
-- statement:
--   The Scheme Coh construction uses the app smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L139-L141

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

theorem GroundTheory.Arith.SchemeCoh.app_smul {P Q : PMod X} (φ : P ⟶ Q) {U : X.Opens} (r : ringOn X U) (x : P.obj (op U)) :
    φ.app (op U) (r • x) = r • φ.app (op U) x := by sorry
