-- Prove2me | Theorems.Thm_GlobalTheory_lattice_inequality
-- name    : GlobalTheory.lattice_inequality
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:02:13.485185+00:00
-- url     : https://prove2.me/theorems/ca68e8f6-b0eb-46cb-92cb-1313f182d9b4
-- title:
--   Global Theory: lattice inequality
-- statement:
--   The Global Theory construction uses the lattice inequality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L88-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsReducedCombination.lean#L88-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsReducedCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
open LatticeIneq

theorem GlobalTheory.lattice_inequality :
    ∀ (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ), (∀ x, 0 ≤ q x) → ∀ (I : Type) [Fintype I] (N N' j : ℕ), 1 ≤ N → N ∣ N' → 1 ≤ j → ∀ (yy w : I → X) (vth : I → ℝ) (αs c : X) (vf' : ℝ), (∀ x, ∃ μ, w x = yy x + N' • μ) → (∀ x, q (w x) ≤ (N' : ℝ) ^ 2 * vth x) → q αs ≤ N * vf' → c - αs ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ) → ∃ μ : X, j * (q (c + N • μ) / N) ≤ (j + 1) * vf' + (j * (j + 1) * Fintype.card I * N * N' ^ 2 : ℕ) * ∑ x, vth x := by sorry
