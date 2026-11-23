-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isInt_gal
-- name    : GlobalTheory.K5.Basic.isInt_gal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:08.913789+00:00
-- url     : https://prove2.me/theorems/1c306db4-3f52-4ae2-922d-330555d21f31
-- title:
--   Basic: is Int gal
-- statement:
--   The Basic construction uses the is Int gal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L362-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L362-L363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem GlobalTheory.K5.Basic.isInt_gal (g : Gal p Ω) {x : Ω} (hx : IsInt p x) : IsInt p (g x) := by sorry
