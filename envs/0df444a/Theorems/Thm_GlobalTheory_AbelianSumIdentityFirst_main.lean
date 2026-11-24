-- Prove2me | Theorems.Thm_GlobalTheory_AbelianSumIdentityFirst_main
-- name    : GlobalTheory.AbelianSumIdentityFirst.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:52:20.932226+00:00
-- url     : https://prove2.me/theorems/a503d883-00e4-48b3-a444-21894b0cba8a
-- title:
--   Abelian Sum Identity First: main
-- statement:
--   The Abelian Sum Identity First construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerTail.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ImportsTerTail.lean#L5-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.AbelianSumIdentityFirst

theorem GlobalTheory.AbelianSumIdentityFirst.main : ∀ {ι : Type} {z : ℂ}, z ≠ (0 : ℂ) → ∀ (s : Finset ι) (a : ι → ℤ),
    z ^ ∑ i ∈ s, a i = ∏ i ∈ s, z ^ a i := by sorry
