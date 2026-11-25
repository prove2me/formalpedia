-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_map_quotient_add_one_le
-- name    : GroundTheory.Arith.Abelian.Jacobian.height_map_quotient_add_one_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:06.745155+00:00
-- url     : https://prove2.me/theorems/a7c27569-ddca-4d6a-84ed-ed491edc59aa
-- title:
--   Jacobian: height map quotient add one le
-- statement:
--   The Jacobian construction uses the height map quotient add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L201-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L201-L226

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
omit [Algebra k A] [Algebra.FiniteType k A]

theorem GroundTheory.Arith.Abelian.Jacobian.height_map_quotient_add_one_le [IsNoetherianRing A] {p₁ p : Ideal A} [p₁.IsPrime]
    [p.IsPrime] (h : p₁ ≤ p) (h0 : p₁ ≠ ⊥) :
    (p.map (Ideal.Quotient.mk p₁)).height + 1 ≤ p.height := by sorry
