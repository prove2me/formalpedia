-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_exists_isKum
-- name    : GlobalTheory.K5.Basic.exists_isKum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:42:11.886553+00:00
-- url     : https://prove2.me/theorems/75570807-63f9-4af5-8bb2-1ea37fc82655
-- title:
--   Basic: exists is Kum
-- statement:
--   The Basic construction uses the exists is Kum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L425-L438
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L425-L438

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

theorem GlobalTheory.K5.Basic.exists_isKum (T : Tower p Ω) (n : ℕ) (H : Subgroup (Gal p Ω)) {r : Ω} (hr : r ≠ 0)
    (hH : ∀ g ∈ H, g (r ^ p ^ n) = r ^ p ^ n) : ∃ a, IsKum T n H r a := by sorry
