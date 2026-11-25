-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isKum_unique
-- name    : GlobalTheory.K5.Basic.isKum_unique
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:13:19.524492+00:00
-- url     : https://prove2.me/theorems/200c1d5b-6a56-46a8-a658-d1b4e7de3bdd
-- title:
--   Basic: is Kum unique
-- statement:
--   The Basic construction uses the is Kum unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L443-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L443-L449

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

theorem GlobalTheory.K5.Basic.isKum_unique {T : Tower p Ω} {n : ℕ} {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0)
    {a b : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H r a) (hb : IsKum T n H r b) {g : Gal p Ω}
    (hg : g ∈ H) : a g = b g := by sorry
