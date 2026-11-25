-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Isogeny_comap_genY
-- name    : GroundTheory.Arith.Abelian.Isogeny.comap_genY
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:57:54.992927+00:00
-- url     : https://prove2.me/theorems/540612ca-59bb-46b2-a1b3-63ca045c832d
-- title:
--   Isogeny: comap gen Y
-- statement:
--   The Isogeny construction uses the comap gen Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L76-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L76-L76

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
variable (E E' : WeierstrassCurve F) [E.IsElliptic] [E'.IsElliptic]
open GroundTheory.Arith.Abelian.Isogeny
variable {E E'} (φ : Isogeny E E')
omit [E.IsElliptic] [E'.IsElliptic]

theorem GroundTheory.Arith.Abelian.Isogeny.comap_genY : φ.comap (genY E') = φ.y := by sorry
