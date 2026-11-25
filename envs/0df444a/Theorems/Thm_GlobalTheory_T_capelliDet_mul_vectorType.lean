-- Prove2me | Theorems.Thm_GlobalTheory_T_capelliDet_mul_vectorType
-- name    : GlobalTheory.T.capelliDet_mul_vectorType
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:44:57.371805+00:00
-- url     : https://prove2.me/theorems/8dc9213e-8117-5ef7-9e3d-49875505023f
-- title:
--   T: capelli Det mul vector Type
-- statement:
--   The T construction uses the capelli Det mul vector Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliDetMulVectorTypeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CapelliDetMulVectorTypeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliDetMulVectorType
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CapelliDetMulVectorTypeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.capelliDet_mul_vectorType : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (x : Fin (m + 1) → A), GlRel E → (∀ a b j, E a b * x j = x j * E a b + if b = j then x a else 0) → ∀ (u : ℂ) (j : Fin (m + 1)), qdet E u * x j = x j * qdet E u + ∑ a : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (j : ℕ))) • (x a * qminor E (Fin.succAbove a) (Fin.succAbove j) (u - 1)) := by sorry
