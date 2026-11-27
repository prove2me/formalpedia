-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_degree_mulIsogeny
-- name    : GroundTheory.Arith.Abelian.degree_mulIsogeny
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:52:39.991575+00:00
-- url     : https://prove2.me/theorems/ba11f501-6ede-5e4a-8120-4a419251d0bc
-- title:
--   Abelian: degree mul Isogeny
-- statement:
--   The Abelian construction uses the degree mul Isogeny property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L223-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Isogeny.lean#L223-L257

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

theorem GroundTheory.Arith.Abelian.degree_mulIsogeny {n : ℤ} (hn : n ≠ 0) : (mulIsogeny E n hn).degree = n.natAbs ^ 2 := by sorry
