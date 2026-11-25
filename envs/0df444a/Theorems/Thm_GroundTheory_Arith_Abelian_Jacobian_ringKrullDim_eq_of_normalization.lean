-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_of_normalization
-- name    : GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:51:41.26306+00:00
-- url     : https://prove2.me/theorems/ed71ef64-a2d5-4d9d-98cf-0efd5291973d
-- title:
--   Jacobian: ring Krull Dim eq of normalization
-- statement:
--   The Jacobian construction uses the ring Krull Dim eq of normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L14-L20

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

theorem GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) : ringKrullDim A = s := by sorry
