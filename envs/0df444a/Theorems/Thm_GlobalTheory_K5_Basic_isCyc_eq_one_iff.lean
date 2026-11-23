-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isCyc_eq_one_iff
-- name    : GlobalTheory.K5.Basic.isCyc_eq_one_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:01.087129+00:00
-- url     : https://prove2.me/theorems/d6388529-db92-4e99-af73-d3efbed8a2d3
-- title:
--   Basic: is Cyc eq one iff
-- statement:
--   The Basic construction uses the is Cyc eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L480-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L480-L487

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

theorem GlobalTheory.K5.Basic.isCyc_eq_one_iff {T : Tower p Ω} {k : ℕ} {χ : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (g : Gal p Ω) : χ g = 1 ↔ g (T.ζ k) = T.ζ k := by sorry
