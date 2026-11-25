-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_trdeg_eq_of_normalization
-- name    : GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:55:48.709214+00:00
-- url     : https://prove2.me/theorems/a6401977-f5a1-5733-87c9-4302b9a6d040
-- title:
--   Jacobian: trdeg eq of normalization
-- statement:
--   The Jacobian construction uses the trdeg eq of normalization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L22-L32

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

theorem GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization [IsDomain A] {s : ℕ} (g : MvPolynomial (Fin s) k →ₐ[k] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) : trdeg k A = s := by sorry
