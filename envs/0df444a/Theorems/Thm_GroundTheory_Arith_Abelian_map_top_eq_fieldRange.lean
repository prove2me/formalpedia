-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_map_top_eq_fieldRange
-- name    : GroundTheory.Arith.Abelian.map_top_eq_fieldRange
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:10.100587+00:00
-- url     : https://prove2.me/theorems/a8391860-55b1-4448-8211-2fb9a4d0bb52
-- title:
--   Abelian: map top eq field Range
-- statement:
--   The Abelian construction uses the map top eq field Range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L111-L114

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

theorem GroundTheory.Arith.Abelian.map_top_eq_fieldRange {K L : Type*} [Field K] [Field L] [Algebra F K] [Algebra F L]
    (f : K →ₐ[F] L) : (⊤ : IntermediateField F K).map f = f.fieldRange := by sorry
