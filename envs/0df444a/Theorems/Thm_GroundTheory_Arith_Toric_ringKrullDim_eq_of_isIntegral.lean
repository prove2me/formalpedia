-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_eq_of_isIntegral
-- name    : GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:41.262801+00:00
-- url     : https://prove2.me/theorems/7884564c-d4d6-4040-b7dd-531d6f8a3072
-- title:
--   Toric: ring Krull Dim eq of is Integral
-- statement:
--   The Toric construction uses the ring Krull Dim eq of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L50-L52

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

theorem GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R := by sorry
