-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_mul
-- name    : GroundTheory.Arith.Iwasawa.IsDistinguished.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:55.158202+00:00
-- url     : https://prove2.me/theorems/71885cb3-b2be-4eee-a162-0476391a6519
-- title:
--   Is Distinguished: mul
-- statement:
--   The Is Distinguished construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L76-L78

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Iwasawa
open PowerSeries IsLocalRing
open scoped Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}

theorem GroundTheory.Arith.Iwasawa.IsDistinguished.mul {P Q : ℤ_[p][X]} (hP : IsDistinguished p P)
    (hQ : IsDistinguished p Q) : IsDistinguished p (P * Q) := by sorry
