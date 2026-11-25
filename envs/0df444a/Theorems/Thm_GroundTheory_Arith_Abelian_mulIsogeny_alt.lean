-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_mulIsogeny_alt
-- name    : GroundTheory.Arith.Abelian.mulIsogeny_alt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:34:15.666523+00:00
-- url     : https://prove2.me/theorems/dbf1620c-10e4-42a4-9cc5-03c9e1667b8f
-- title:
--   Abelian: mul Isogeny alt
-- statement:
--   The Abelian construction uses the mul Isogeny alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L209-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L209-L211

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_FunctionFieldPoint
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
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
universe u
variable {F : Type u} [Field F]
variable (E : WeierstrassCurve F) [E.IsElliptic]

theorem GroundTheory.Arith.Abelian.mulIsogeny_alt {n : ℤ} (hn : n ≠ 0) :
    (mulIsogeny E n hn).x = aeval (genX E) (E.Φ n) / aeval (genX E) (E.ΨSq n) := by sorry
