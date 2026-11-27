-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_topologicalKrullDim_affineToricVariety
-- name    : GroundTheory.Arith.Toric.topologicalKrullDim_affineToricVariety
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:52:48.294313+00:00
-- url     : https://prove2.me/theorems/135595c5-e068-5d82-a309-39fb68b5a320
-- title:
--   Toric: topological Krull Dim affine Toric Variety
-- statement:
--   The Toric construction uses the topological Krull Dim affine Toric Variety property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L158-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean#L158-L161

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
variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

theorem GroundTheory.Arith.Toric.topologicalKrullDim_affineToricVariety {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hs : (σ : ConvexCone ℝ (ℝ ⊗[ℤ] N)).Salient) :
    topologicalKrullDim (PrimeSpectrum (toricAlgebra k σ)) = Module.finrank ℤ N := by sorry
