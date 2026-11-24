-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_of_alt
-- name    : GroundTheory.Arith.SchemeCoh.IsBasisOn.map_of_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:40.932399+00:00
-- url     : https://prove2.me/theorems/6ef9b802-b5dc-4d81-aed0-c7d4b2bf48e5
-- title:
--   Is Basis On: map of alt
-- statement:
--   The Is Basis On construction uses the map of alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L152-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L152-L218

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

theorem GroundTheory.Arith.SchemeCoh.IsBasisOn.map_of_alt {P : PMod X} {F : X.Modules} (φ : P ⟶ (preMod X).obj F)
    (hφ : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj φ)
    {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s) :
    IsBasisOn ((preMod X).obj F) U (φ.app _ s) := by sorry
