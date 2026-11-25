-- Prove2me | Theorems.Thm_GlobalTheory_BandLemmaThird_main
-- name    : GlobalTheory.BandLemmaThird.main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:56:40.92367+00:00
-- url     : https://prove2.me/theorems/288daae1-b7bd-54d3-bd36-5b77b8c57d81
-- title:
--   Band Lemma Third: main
-- statement:
--   The Band Lemma Third construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherMore.lean#L7-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsFurtherMore.lean#L7-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsFurtherMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.BandLemmaThird

theorem GlobalTheory.BandLemmaThird.main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [inst_1 : Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {i j : ℕ} {X Y : Matrix ι ι k}, d1 ℓ i X → d1 ℓ j Y → d1 ℓ (i + j) (X * Y)) := by sorry
