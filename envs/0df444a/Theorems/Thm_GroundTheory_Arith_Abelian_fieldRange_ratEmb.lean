-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_fieldRange_ratEmb
-- name    : GroundTheory.Arith.Abelian.fieldRange_ratEmb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:30:45.555735+00:00
-- url     : https://prove2.me/theorems/673c6df7-b4d5-4d5e-bd8f-4957e2b6b3a4
-- title:
--   Abelian: field Range rat Emb
-- statement:
--   The Abelian construction uses the field Range rat Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L117-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L117-L118

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
omit [E.IsElliptic]

theorem GroundTheory.Arith.Abelian.fieldRange_ratEmb : (ratEmb E).fieldRange = F⟮genX E⟯ := by sorry
