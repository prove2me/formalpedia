-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isKum_mul
-- name    : GlobalTheory.K5.Basic.isKum_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:42:01.912595+00:00
-- url     : https://prove2.me/theorems/05c1340c-aa85-4419-a74a-c1168cb62d53
-- title:
--   Basic: is Kum mul
-- statement:
--   The Basic construction uses the is Kum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L498-L509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L498-L509

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

theorem GlobalTheory.K5.Basic.isKum_mul {T : Tower p Ω} {n : ℕ} {χ : Gal p Ω → ZMod (p ^ n)}
    (hχ : ∀ g : Gal p Ω, g (T.ζ n) = T.ζ n ^ (χ g).val)
    {H : Subgroup (Gal p Ω)} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n H r a) {g h : Gal p Ω} (hg : g ∈ H) (hh : h ∈ H) :
    a (g * h) = a g + χ g * a h := by sorry
