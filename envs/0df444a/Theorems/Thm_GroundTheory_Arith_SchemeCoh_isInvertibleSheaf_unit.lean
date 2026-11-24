-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_isInvertibleSheaf_unit
-- name    : GroundTheory.Arith.SchemeCoh.isInvertibleSheaf_unit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:28:12.999851+00:00
-- url     : https://prove2.me/theorems/65d93dff-4549-4498-adce-24481b1e9974
-- title:
--   Scheme Coh: is Invertible Sheaf unit
-- statement:
--   The Scheme Coh construction uses the is Invertible Sheaf unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L268-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L268-L269

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

theorem GroundTheory.Arith.SchemeCoh.isInvertibleSheaf_unit : IsInvertibleSheaf (𝟙_ X.Modules) := by sorry
