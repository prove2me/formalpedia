-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_trdeg_eq_of_isFractionRing
-- name    : GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:52:33.408902+00:00
-- url     : https://prove2.me/theorems/cd411420-9790-4170-8a16-90034f25aef9
-- title:
--   Jacobian: trdeg eq of is Fraction Ring
-- statement:
--   The Jacobian construction uses the trdeg eq of is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L57-L62

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
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]
omit [Algebra.FiniteType k A]

theorem GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [Algebra k K] [IsScalarTower k A K] : trdeg k K = trdeg k A := by sorry
