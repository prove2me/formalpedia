-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_ringKrullDim_le_of_isIntegral
-- name    : GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:43:16.542435+00:00
-- url     : https://prove2.me/theorems/754eab76-9a24-402e-9f7a-67cbd6ac7348
-- title:
--   Toric: ring Krull Dim le of is Integral
-- statement:
--   The Toric construction uses the ring Krull Dim le of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L14-L16

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

theorem GroundTheory.Arith.Toric.ringKrullDim_le_of_isIntegral : ringKrullDim A ≤ ringKrullDim R := by sorry
