-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_sub_one_le_trdeg_quotient_span_prime
-- name    : GroundTheory.Arith.Abelian.Jacobian.sub_one_le_trdeg_quotient_span_prime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:56:21.604187+00:00
-- url     : https://prove2.me/theorems/537c769e-d8e9-4db6-8480-3b5fde0402c5
-- title:
--   Jacobian: sub one le trdeg quotient span prime
-- statement:
--   The Jacobian construction uses the sub one le trdeg quotient span prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L87-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean#L87-L128

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
variable (k : Type u) [Field k]

theorem GroundTheory.Arith.Abelian.Jacobian.sub_one_le_trdeg_quotient_span_prime {s : ℕ} {g : MvPolynomial (Fin s) k} (hg : Prime g) :
    ((s - 1 : ℕ) : Cardinal) ≤ trdeg k (MvPolynomial (Fin s) k ⧸ Ideal.span {g}) := by sorry
