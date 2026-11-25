-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient
-- name    : GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:52:51.271885+00:00
-- url     : https://prove2.me/theorems/dffc3042-e671-5863-b3c0-08d54c6aac98
-- title:
--   Jacobian: height add ring Krull Dim quotient
-- statement:
--   The Jacobian construction uses the height add ring Krull Dim quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L276-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L276-L285

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

theorem GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (p : Ideal A) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by sorry
