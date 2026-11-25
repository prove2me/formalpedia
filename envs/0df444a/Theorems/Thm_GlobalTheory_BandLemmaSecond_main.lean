-- Prove2me | Theorems.Thm_GlobalTheory_BandLemmaSecond_main
-- name    : GlobalTheory.BandLemmaSecond.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:55.014018+00:00
-- url     : https://prove2.me/theorems/5a1fcbb4-a6d4-4c0b-990c-439f0004ce81
-- title:
--   Band Lemma Second: main
-- statement:
--   The Band Lemma Second construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherTer.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherTer.lean#L7-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandLemmaSecond

theorem GlobalTheory.BandLemmaSecond.main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j (-X)) := by sorry
