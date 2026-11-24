-- Prove2me | Theorems.Thm_GroundTheory_Arith_Jacobian_ker_le_maximalIdeal
-- name    : GroundTheory.Arith.Jacobian.ker_le_maximalIdeal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:53.400512+00:00
-- url     : https://prove2.me/theorems/1f5350c8-014b-4dc3-85f8-9e8cb3d1d64f
-- title:
--   Jacobian: ker le maximal Ideal
-- statement:
--   The Jacobian construction uses the ker le maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L77-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/SmoothOfRegular.lean#L77-L80

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
omit [Algebra k P] [Algebra k S] [IsScalarTower k P S]
include hsurj

theorem GroundTheory.Arith.Jacobian.ker_le_maximalIdeal : RingHom.ker (algebraMap P S) ≤ maximalIdeal P := by sorry
