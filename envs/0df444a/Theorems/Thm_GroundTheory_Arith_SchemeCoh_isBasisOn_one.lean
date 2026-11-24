-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isBasisOn_one
-- name    : GroundTheory.Arith.SchemeCoh.isBasisOn_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:26:40.971646+00:00
-- url     : https://prove2.me/theorems/ea69e83c-be52-4c5f-b8e5-5802c2629c7a
-- title:
--   Scheme Coh: is Basis On one
-- statement:
--   The Scheme Coh construction uses the is Basis On one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L227-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L227-L235

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

theorem GroundTheory.Arith.SchemeCoh.isBasisOn_one (U : X.Opens) :
    IsBasisOn ((preMod X).obj (𝟙_ X.Modules)) U (1 : ringOn X U) := by sorry
