-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_relfinrank_adjoin_genX_pow
-- name    : GroundTheory.Arith.Abelian.relfinrank_adjoin_genX_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:39:43.228467+00:00
-- url     : https://prove2.me/theorems/c87174fd-419d-4d5b-8592-f1cef867c5cd
-- title:
--   Abelian: relfinrank adjoin gen X pow
-- statement:
--   The Abelian construction uses the relfinrank adjoin gen X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L198-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/IsogenyFrobenius.lean#L198-L208

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

theorem GroundTheory.Arith.Abelian.relfinrank_adjoin_genX_pow :
    relfinrank F⟮genX E ^ p⟯ F⟮genX E⟯ = p := by sorry
