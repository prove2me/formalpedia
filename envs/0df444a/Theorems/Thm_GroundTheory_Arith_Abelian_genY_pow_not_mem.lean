-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_genY_pow_not_mem
-- name    : GroundTheory.Arith.Abelian.genY_pow_not_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:40:36.499827+00:00
-- url     : https://prove2.me/theorems/6d3b61da-d244-4cc4-9f39-cf2bb4d3d25e
-- title:
--   Abelian: gen Y pow not mem
-- statement:
--   The Abelian construction uses the gen Y pow not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L210-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L210-L218

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
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]

theorem GroundTheory.Arith.Abelian.genY_pow_not_mem : genY E ^ p ∉ F⟮genX E ^ p⟯ := by sorry
