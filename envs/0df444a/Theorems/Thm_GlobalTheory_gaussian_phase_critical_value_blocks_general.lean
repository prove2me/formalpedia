-- Prove2me | Theorems.Thm_GlobalTheory_gaussian_phase_critical_value_blocks_general
-- name    : GlobalTheory.gaussian_phase_critical_value_blocks_general
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:15.834679+00:00
-- url     : https://prove2.me/theorems/739dfda2-0da2-448a-8a67-047687ad5130
-- title:
--   Global Theory: gaussian phase critical value blocks general
-- statement:
--   The Global Theory construction uses the gaussian phase critical value blocks general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPhaseCriticalValueBlocksGeneral.lean#L11-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GaussianPhaseCriticalValueBlocksGeneral.lean#L11-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GaussianPhaseCriticalValueBlocksGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory

theorem GlobalTheory.gaussian_phase_critical_value_blocks_general {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (C : Matrix n m ℂ) (B : Matrix m n ℂ)
    (a c : m → ℂ) (b d : n → ℂ) (hN : IsUnit (1 - C * B).det) :
    let S : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 Cᵀ C 0
    let T : Matrix (m ⊕ n) (m ⊕ n) ℂ := fromBlocks 0 B Bᵀ 0
    let w : m ⊕ n → ℂ := (1 - T * S)⁻¹ *ᵥ (Sum.elim c d + T *ᵥ Sum.elim a b)
    let u : m ⊕ n → ℂ := Sum.elim a b + S *ᵥ w
    1 / 2 * (Sum.elim a b ⬝ᵥ w + Sum.elim c d ⬝ᵥ u)
      = a ⬝ᵥ (1 - B * C)⁻¹ *ᵥ c + d ⬝ᵥ (1 - C * B)⁻¹ *ᵥ b
        + a ⬝ᵥ ((1 - B * C)⁻¹ * B) *ᵥ b + d ⬝ᵥ ((1 - C * B)⁻¹ * C) *ᵥ c := by sorry
