-- Prove2me | Theorems.Thm_GlobalTheory_shortExact_mul_p_modP
-- name    : GlobalTheory.shortExact_mul_p_modP
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:20:45.307628+00:00
-- url     : https://prove2.me/theorems/c741d498-a8fe-4304-857a-15cbeb9557be
-- title:
--   Global Theory: short Exact mul p mod P
-- statement:
--   The Global Theory construction uses the short Exact mul p mod P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L119-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean#L119-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
open GlobalTheory

theorem GlobalTheory.shortExact_mul_p_modP :
    ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime],
      (∀ (n : ℕ) (x : C.X n), (p : ℤ) • x = 0 → x = 0) →
      ∃ (π : C ⟶ ((ModuleCat.restrictScalars.{0} (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (((ModuleCat.extendScalars (Int.castRingHom (ZMod p))).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj C)) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0),
        (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact := by sorry
