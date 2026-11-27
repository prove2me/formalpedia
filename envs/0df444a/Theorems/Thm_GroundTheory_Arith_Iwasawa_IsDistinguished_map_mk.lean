-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_map_mk
-- name    : GroundTheory.Arith.Iwasawa.IsDistinguished.map_mk
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:37.772587+00:00
-- url     : https://prove2.me/theorems/d36e3b58-0fbf-44b1-b6e8-c7465119e22f
-- title:
--   Is Distinguished: map mk
-- statement:
--   The Is Distinguished construction uses the map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L83-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L83-L86

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

theorem GroundTheory.Arith.Iwasawa.IsDistinguished.map_mk {P : ℤ_[p][X]} (hP : IsDistinguished p P) :
    (P : Lambda p).map (Ideal.Quotient.mk (maximalIdeal ℤ_[p])) = X ^ P.natDegree := by sorry
