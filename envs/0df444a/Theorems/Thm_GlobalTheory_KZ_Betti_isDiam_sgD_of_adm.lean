-- Prove2me | Theorems.Thm_GlobalTheory_KZ_Betti_isDiam_sgD_of_adm
-- name    : GlobalTheory.KZ.Betti.isDiam_sgD_of_adm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:49.885709+00:00
-- url     : https://prove2.me/theorems/ac76543d-f520-51fc-bf51-28028bae09e8
-- title:
--   Betti: is Diam sg D of adm
-- statement:
--   The Betti construction uses the is Diam sg D of adm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/OpLDOneSubMemTriv.lean#L111-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Letter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_OpLDOneSubMemTriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix
open GlobalTheory GlobalTheory.KZ
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
open GlobalTheory.KZ.Betti

theorem GlobalTheory.KZ.Betti.isDiam_sgD_of_adm {N l q : ℕ} (h : admitted N l (Letter.T q)) : IsDiam N l q (sgD N l q) := by sorry
