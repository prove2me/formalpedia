-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_isNoetherianRing
-- name    : GroundTheory.Arith.Iwasawa.isNoetherianRing
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:26:27.427736+00:00
-- url     : https://prove2.me/theorems/6ae17d40-3aba-4874-8027-78541612637d
-- title:
--   Iwasawa: is Noetherian Ring
-- statement:
--   The Iwasawa construction uses the is Noetherian Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L19-L19

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

theorem GroundTheory.Arith.Iwasawa.isNoetherianRing : IsNoetherianRing (Lambda p) := by sorry
