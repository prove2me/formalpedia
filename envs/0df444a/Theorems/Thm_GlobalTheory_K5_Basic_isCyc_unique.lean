-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_isCyc_unique
-- name    : GlobalTheory.K5.Basic.isCyc_unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:11:41.07934+00:00
-- url     : https://prove2.me/theorems/cdf970eb-13af-5f56-9a28-2043175a3dbc
-- title:
--   Basic: is Cyc unique
-- statement:
--   The Basic construction uses the is Cyc unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L462-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L462-L469

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

theorem GlobalTheory.K5.Basic.isCyc_unique {T : Tower p Ω} {k : ℕ} {χ χ' : Gal p Ω → ZMod (p ^ k)}
    (h : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val)
    (h' : ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ' g).val) : χ = χ' := by sorry
