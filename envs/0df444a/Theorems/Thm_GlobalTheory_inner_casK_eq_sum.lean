-- Prove2me | Theorems.Thm_GlobalTheory_inner_casK_eq_sum
-- name    : GlobalTheory.inner_casK_eq_sum
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:22.114551+00:00
-- url     : https://prove2.me/theorems/c570547a-973f-4c8d-92a1-2b12f2b21dc0
-- title:
--   Global Theory: inner cas K eq sum
-- statement:
--   The Global Theory construction uses the inner cas K eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CasKIsSymmetricAndForm.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CasKIsSymmetricAndForm.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CasKIsSymmetricAndForm
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
open GlobalTheory

theorem GlobalTheory.inner_casK_eq_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by sorry
