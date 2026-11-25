-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_roots_toFinset_sq
-- name    : GroundTheory.Arith.Abelian.roots_toFinset_sq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:05.233738+00:00
-- url     : https://prove2.me/theorems/6b613fab-384e-41d0-8606-08d6842a71a1
-- title:
--   Abelian: roots to Finset sq
-- statement:
--   The Abelian construction uses the roots to Finset sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L84-L85

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
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
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [E.IsElliptic]
  (p : ℕ) [hp : Fact p.Prime] [CharP F p]

theorem GroundTheory.Arith.Abelian.roots_toFinset_sq (q : F[X]) : (q ^ 2).roots.toFinset = q.roots.toFinset := by sorry
