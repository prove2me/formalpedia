-- Prove2me | Theorems.Thm_GlobalTheory_charpoly_nilpotent_add_scalar
-- name    : GlobalTheory.charpoly_nilpotent_add_scalar
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:43.999569+00:00
-- url     : https://prove2.me/theorems/d784eeab-f327-4df6-990b-a62745e41c3e
-- title:
--   Global Theory: charpoly nilpotent add scalar
-- statement:
--   The Global Theory construction uses the charpoly nilpotent add scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyNilpotentAddScalar.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CharpolyNilpotentAddScalar.lean#L7-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyNilpotentAddScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.charpoly_nilpotent_add_scalar : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by sorry
