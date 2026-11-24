-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_normEDS_invariant
-- name    : GroundTheory.Arith.Abelian.normEDS_invariant
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:25:23.512857+00:00
-- url     : https://prove2.me/theorems/5fe75978-e4a4-4c28-aa53-579279ba7746
-- title:
--   Abelian: norm EDS invariant
-- statement:
--   The Abelian construction uses the norm EDS invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/NormEDS.lean#L245-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/NormEDS.lean#L245-L254

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
variable {R : Type*} [CommRing R] (b c d : R)

theorem GroundTheory.Arith.Abelian.normEDS_invariant (n : ℤ) :
    c * (normEDS b c d (n + 2) * normEDS b c d (n - 1) ^ 2 +
        normEDS b c d (n - 2) * normEDS b c d (n + 1) ^ 2) =
      (b ^ 4 + d) * normEDS b c d (n - 1) * normEDS b c d n * normEDS b c d (n + 1) -
        b ^ 2 * c * normEDS b c d n ^ 3 := by sorry
