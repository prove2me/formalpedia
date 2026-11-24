-- Prove2me | Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsBasisOn_restrict
-- name    : GroundTheory.Arith.SchemeCoh.IsBasisOn.restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:26:47.646157+00:00
-- url     : https://prove2.me/theorems/456014b0-c3fd-482f-b6b5-168ece3794dd
-- title:
--   Is Basis On: restrict
-- statement:
--   The Is Basis On construction uses the restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L220-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/InvertibleSheaf.lean#L220-L225

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

theorem GroundTheory.Arith.SchemeCoh.IsBasisOn.restrict {P : PMod X} {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s)
    {V : X.Opens} (h : V ≤ U) : IsBasisOn P V (resM P h s) := by sorry
