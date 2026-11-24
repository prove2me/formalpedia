-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_resM
-- name    : GroundTheory.Arith.SchemeCoh.app_resM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:21.356857+00:00
-- url     : https://prove2.me/theorems/50af1222-eabd-4328-816a-742e82dab427
-- title:
--   Scheme Coh: app res M
-- statement:
--   The Scheme Coh construction uses the app res M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L135-L137

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

theorem GroundTheory.Arith.SchemeCoh.app_resM {P Q : PMod X} (φ : P ⟶ Q) {U V : X.Opens} (h : V ≤ U) (x : P.obj (op U)) :
    φ.app (op V) (resM P h x) = resM Q h (φ.app (op U) x) := by sorry
