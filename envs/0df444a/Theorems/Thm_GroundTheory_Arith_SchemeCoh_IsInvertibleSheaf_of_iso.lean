-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsInvertibleSheaf_of_iso
-- name    : GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.of_iso
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:22.2438+00:00
-- url     : https://prove2.me/theorems/5a81b847-6bfc-488e-ba87-3eb365778ff9
-- title:
--   Is Invertible Sheaf: of iso
-- statement:
--   The Is Invertible Sheaf construction uses the of iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L271-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L271-L275

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

theorem GroundTheory.Arith.SchemeCoh.IsInvertibleSheaf.of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsInvertibleSheaf M) :
    IsInvertibleSheaf N := by sorry
