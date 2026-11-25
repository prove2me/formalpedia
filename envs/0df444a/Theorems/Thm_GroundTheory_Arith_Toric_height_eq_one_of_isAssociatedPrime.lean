-- Prove2me | Theorems.Thm_GroundTheory_Arith_Toric_height_eq_one_of_isAssociatedPrime
-- name    : GroundTheory.Arith.Toric.height_eq_one_of_isAssociatedPrime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:13.698382+00:00
-- url     : https://prove2.me/theorems/4bc78d5f-7e51-4ea5-af70-79215bf010db
-- title:
--   Toric: height eq one of is Associated Prime
-- statement:
--   The Toric construction uses the height eq one of is Associated Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L15-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/KrullDomain.lean#L15-L71

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

theorem GroundTheory.Arith.Toric.height_eq_one_of_isAssociatedPrime {b : A} (hb : b ≠ 0) {P : Ideal A}
    (hP : IsAssociatedPrime P (A ⧸ Ideal.span {b})) : P.height = 1 := by sorry
