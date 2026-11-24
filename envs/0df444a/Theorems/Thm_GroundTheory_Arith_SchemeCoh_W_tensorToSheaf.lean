-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_W_tensorToSheaf
-- name    : GroundTheory.Arith.SchemeCoh.W_tensorToSheaf
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:34.281866+00:00
-- url     : https://prove2.me/theorems/ff177421-7a0d-47b9-b6a6-fae11bda86e7
-- title:
--   Scheme Coh: W tensor To Sheaf
-- statement:
--   The Scheme Coh construction uses the W tensor To Sheaf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L74-L79

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

theorem GroundTheory.Arith.SchemeCoh.W_tensorToSheaf (M N : X.Modules) :
    ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj (tensorToSheaf M N) := by sorry
