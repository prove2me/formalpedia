-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_IsDistinguished_ne_zero
-- name    : GroundTheory.Arith.Iwasawa.IsDistinguished.ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:00.502273+00:00
-- url     : https://prove2.me/theorems/298ef2b7-be89-4bfb-8a15-9fad7de1d059
-- title:
--   Is Distinguished: ne zero
-- statement:
--   The Is Distinguished construction uses the ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L80-L81

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

theorem GroundTheory.Arith.Iwasawa.IsDistinguished.ne_zero {P : ℤ_[p][X]} (hP : IsDistinguished p P) : P ≠ 0 := by sorry
