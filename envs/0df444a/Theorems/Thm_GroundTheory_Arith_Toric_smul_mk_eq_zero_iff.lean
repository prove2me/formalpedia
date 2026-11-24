-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_smul_mk_eq_zero_iff
-- name    : GroundTheory.Arith.Toric.smul_mk_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:32.242809+00:00
-- url     : https://prove2.me/theorems/940b6b7a-cc3b-4818-a536-8fcae0af7bcd
-- title:
--   Toric: smul mk eq zero iff
-- statement:
--   The Toric construction uses the smul mk eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L10-L13

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]

theorem GroundTheory.Arith.Toric.smul_mk_eq_zero_iff {b r y : A} :
    r • (Ideal.Quotient.mk (Ideal.span {b}) y) = 0 ↔ b ∣ r * y := by sorry
