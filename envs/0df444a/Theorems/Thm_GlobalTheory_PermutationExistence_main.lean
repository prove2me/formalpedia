-- Prove2me | Theorems.Thm_GlobalTheory_PermutationExistence_main
-- name    : GlobalTheory.PermutationExistence.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:13:10.105219+00:00
-- url     : https://prove2.me/theorems/7bedccd3-3711-51b8-b905-d71b71418c03
-- title:
--   Permutation Existence: main
-- statement:
--   The Permutation Existence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsRest.lean#L39-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ImportsRest.lean#L39-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ImportsRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.PermutationExistence

theorem GlobalTheory.PermutationExistence.main {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by sorry
