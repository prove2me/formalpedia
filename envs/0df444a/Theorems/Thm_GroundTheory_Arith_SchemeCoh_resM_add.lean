-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_add
-- name    : GroundTheory.Arith.SchemeCoh.resM_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:29:23.081442+00:00
-- url     : https://prove2.me/theorems/272a6ddb-b7c7-49e6-ac68-c086fe4890ac
-- title:
--   Scheme Coh: res M add
-- statement:
--   The Scheme Coh construction uses the res M add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L124-L126

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

theorem GroundTheory.Arith.SchemeCoh.resM_add (P : PMod X) {U V : X.Opens} (h : V ≤ U) (x y : P.obj (op U)) :
    resM P h (x + y) = resM P h x + resM P h y := by sorry
