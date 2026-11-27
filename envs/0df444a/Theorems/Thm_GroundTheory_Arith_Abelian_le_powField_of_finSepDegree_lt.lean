-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_le_powField_of_finSepDegree_lt
-- name    : GroundTheory.Arith.Abelian.le_powField_of_finSepDegree_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:59.995525+00:00
-- url     : https://prove2.me/theorems/e773d8e8-6774-5c65-992b-9942901f7515
-- title:
--   Abelian: le pow Field of fin Sep Degree lt
-- statement:
--   The Abelian construction uses the le pow Field of fin Sep Degree lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobeniusSep.lean#L44-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobeniusSep.lean#L44-L89

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]

theorem GroundTheory.Arith.Abelian.le_powField_of_finSepDegree_lt (M : IntermediateField F E.toAffine.FunctionField)
    [FiniteDimensional M E.toAffine.FunctionField]
    (h : Field.finSepDegree M E.toAffine.FunctionField <
      Module.finrank M E.toAffine.FunctionField) : M ≤ powField E p := by sorry
