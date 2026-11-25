-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_le_ringKrullDim_quotient_add_one
-- name    : GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_le_ringKrullDim_quotient_add_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:11.317227+00:00
-- url     : https://prove2.me/theorems/ddc8de8d-6145-4c8b-bee8-1484e29063fe
-- title:
--   Jacobian: ring Krull Dim le ring Krull Dim quotient add one
-- statement:
--   The Jacobian construction uses the ring Krull Dim le ring Krull Dim quotient add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L139-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L139-L188

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
include k

theorem GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_le_ringKrullDim_quotient_add_one (p : Ideal A) [p.IsPrime]
    (hp : p.height = 1) : ringKrullDim A ≤ ringKrullDim (A ⧸ p) + 1 := by sorry
