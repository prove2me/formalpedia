-- Prove2me | Theorems.Thm_GlobalTheory_SkewDense_exists_dual_coef
-- name    : GlobalTheory.SkewDense.exists_dual_coef
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:08.350116+00:00
-- url     : https://prove2.me/theorems/09180fe5-3ee7-4c50-a22b-8bd581a273ee
-- title:
--   Skew Dense: exists dual coef
-- statement:
--   The Skew Dense construction uses the exists dual coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L9-L24

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.SkewDense

theorem GlobalTheory.SkewDense.exists_dual_coef (E : Type) [Field E] [NumberField E] [DecidableEq (E →+* ℂ)] :
    ∃ (κ : Type) (_ : Fintype κ) (b : κ → E) (a : (E →+* ℂ) → κ → ℂ),
      ∀ g₀ g : E →+* ℂ, ∑ k, a g₀ k * g (b k) = if g = g₀ then 1 else 0 := by sorry
