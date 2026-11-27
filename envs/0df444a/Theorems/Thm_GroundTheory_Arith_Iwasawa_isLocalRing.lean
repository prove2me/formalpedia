-- Prove2me | Theorems.Thm_GroundTheory_Arith_Iwasawa_isLocalRing
-- name    : GroundTheory.Arith.Iwasawa.isLocalRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:52:01.775272+00:00
-- url     : https://prove2.me/theorems/382b5666-d759-5f10-bb84-a5723c0e3e4a
-- title:
--   Iwasawa: is Local Ring
-- statement:
--   The Iwasawa construction uses the is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/IwasawaModules/SpanFinrankMaximalIdealLeTwo.lean#L17-L17

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

theorem GroundTheory.Arith.Iwasawa.isLocalRing : IsLocalRing (Lambda p) := by sorry
