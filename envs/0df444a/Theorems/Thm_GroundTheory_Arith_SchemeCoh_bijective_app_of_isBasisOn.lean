-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_bijective_app_of_isBasisOn
-- name    : GroundTheory.Arith.SchemeCoh.bijective_app_of_isBasisOn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:10.086263+00:00
-- url     : https://prove2.me/theorems/234d8312-1d6e-4938-a80a-7fdab2770a2b
-- title:
--   Scheme Coh: bijective app of is Basis On
-- statement:
--   The Scheme Coh construction uses the bijective app of is Basis On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L327-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L327-L338

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

theorem GroundTheory.Arith.SchemeCoh.bijective_app_of_isBasisOn {M N : X.Modules} (f : M ⟶ N) {U : X.Opens}
    {s : ((preMod X).obj M).obj (op U)} (hs : IsBasisOn ((preMod X).obj M) U s)
    (hfs : IsBasisOn ((preMod X).obj N) U (((preMod X).map f).app _ s)) (V : X.Opens) (h : V ≤ U) :
    Function.Bijective (f.app V) := by sorry
