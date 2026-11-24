-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_isDomain
-- name    : GroundTheory.Arith.Iwasawa.isDomain
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:28.454422+00:00
-- url     : https://prove2.me/theorems/491c9219-dc05-4bec-8dc1-bca0e72d32d3
-- title:
--   Iwasawa: is Domain
-- statement:
--   The Iwasawa construction uses the is Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L15-L15

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

theorem GroundTheory.Arith.Iwasawa.isDomain : IsDomain (Lambda p) := by sorry
