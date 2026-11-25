-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_quotient_add_one_le
-- name    : GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:53:03.086902+00:00
-- url     : https://prove2.me/theorems/d7898eb6-fdda-5057-a6d2-5918a6d71fba
-- title:
--   Jacobian: ring Krull Dim quotient add one le
-- statement:
--   The Jacobian construction uses the ring Krull Dim quotient add one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L75-L79

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
variable {A : Type u} [CommRing A] [IsDomain A]

theorem GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le (p : Ideal A) (hp : p ≠ ⊥) :
    ringKrullDim (A ⧸ p) + 1 ≤ ringKrullDim A := by sorry
