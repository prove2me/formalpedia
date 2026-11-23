-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_zeta_pow_eq_iff
-- name    : GlobalTheory.K5.Basic.zeta_pow_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:14:55.926823+00:00
-- url     : https://prove2.me/theorems/3a7d9e31-0226-48c2-9b4c-acbc8930ed01
-- title:
--   Basic: zeta pow eq iff
-- statement:
--   The Basic construction uses the zeta pow eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L420-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L420-L423

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

theorem GlobalTheory.K5.Basic.zeta_pow_eq_iff (T : Tower p Ω) (k a b : ℕ) :
    T.ζ k ^ a = T.ζ k ^ b ↔ a ≡ b [MOD p ^ k] := by sorry
