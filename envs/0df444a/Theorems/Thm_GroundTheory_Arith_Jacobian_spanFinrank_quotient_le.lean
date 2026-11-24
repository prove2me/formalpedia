-- Prove2me | Theorems.Thm_GroundTheory_Arith_Jacobian_spanFinrank_quotient_le
-- name    : GroundTheory.Arith.Jacobian.spanFinrank_quotient_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:16.524566+00:00
-- url     : https://prove2.me/theorems/1a4af072-a597-4ae7-ac55-41c384a69113
-- title:
--   Jacobian: span Finrank quotient le
-- statement:
--   The Jacobian construction uses the span Finrank quotient le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L87-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L87-L144

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Jacobian
open IsLocalRing TensorProduct
universe u
noncomputable section
variable {k : Type u} [Field k] {P S : Type u} [CommRing P] [CommRing S] [Algebra k P]
  [Algebra k S] [Algebra P S] [IsScalarTower k P S] [IsLocalRing P] [IsLocalRing S]
variable (hsurj : Function.Surjective (algebraMap P S))
  (hres : Function.Surjective (algebraMap k (ResidueField S)))
variable [IsNoetherianRing P]
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj

theorem GroundTheory.Arith.Jacobian.spanFinrank_quotient_le (J : Ideal P) [IsLocalRing (P ⧸ J)]
    (hcov : RingHom.ker (algebraMap P S) ≤ J ⊔ maximalIdeal P ^ 2) :
    (maximalIdeal (P ⧸ J)).spanFinrank ≤ (maximalIdeal S).spanFinrank := by sorry
