-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_coheight_eq_ringKrullDim_quotient
-- name    : GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T01:53:15.78159+00:00
-- url     : https://prove2.me/theorems/03189aff-698f-4ecc-a678-9dd984613ce6
-- title:
--   Jacobian: coheight eq ring Krull Dim quotient
-- statement:
--   The Jacobian construction uses the coheight eq ring Krull Dim quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L192-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L192-L197

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
omit [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]

theorem GroundTheory.Arith.Abelian.Jacobian.coheight_eq_ringKrullDim_quotient (p : PrimeSpectrum A) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (A ⧸ p.asIdeal) := by sorry
