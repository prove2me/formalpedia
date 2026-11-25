-- Prove2me | Theorems.Thm_GlobalTheory_WtOrth_exists_decomp
-- name    : GlobalTheory.WtOrth.exists_decomp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:41.471853+00:00
-- url     : https://prove2.me/theorems/4eb951ab-0c44-41f9-b8d7-87d8cd868750
-- title:
--   Wt Orth: exists decomp
-- statement:
--   The Wt Orth construction uses the exists decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecomp.lean#L20-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/WtNearOrthDecomp.lean#L20-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_WtNearOrthDecomp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.WtOrth

theorem GlobalTheory.WtOrth.exists_decomp {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by sorry
