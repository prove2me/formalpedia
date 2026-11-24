-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_map_iso
-- name    : GroundTheory.Arith.SchemeCoh.IsBasisOn.map_iso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:57.106797+00:00
-- url     : https://prove2.me/theorems/3ebde5b7-f9c0-4a7c-8122-eec77ef9b714
-- title:
--   Is Basis On: map iso
-- statement:
--   The Is Basis On construction uses the map iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L259-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L259-L262

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

theorem GroundTheory.Arith.SchemeCoh.IsBasisOn.map_iso {M N : X.Modules} (e : M ≅ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s) :
    IsBasisOn ((preMod X).obj N) U (((preMod X).map e.hom).app _ s) := by sorry
