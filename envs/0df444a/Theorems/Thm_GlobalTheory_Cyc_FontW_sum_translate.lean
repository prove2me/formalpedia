-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_FontW_sum_translate
-- name    : GlobalTheory.Cyc.FontW.sum_translate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:34:46.97863+00:00
-- url     : https://prove2.me/theorems/4cf857e7-08a4-48f3-b756-08d41f4ca97c
-- title:
--   Font W: sum translate
-- statement:
--   The Font W construction uses the sum translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L75-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TensorRight.lean#L75-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW

theorem GlobalTheory.Cyc.FontW.sum_translate {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by sorry
