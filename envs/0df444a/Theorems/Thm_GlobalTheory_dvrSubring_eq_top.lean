-- Prove2me | Theorems.Thm_GlobalTheory_dvrSubring_eq_top
-- name    : GlobalTheory.dvrSubring_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:32.532988+00:00
-- url     : https://prove2.me/theorems/4b16a4d7-8e42-4eda-bcce-9ab4652e1cd7
-- title:
--   Global Theory: dvr Subring eq top
-- statement:
--   The Global Theory construction uses the dvr Subring eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTop.lean#L43-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DvrSubringEqTop.lean#L43-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvrSubringEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.dvrSubring_eq_top (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπS : π ∈ S) (hπ0 : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hinv : ∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (hfrac : ∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) : S = ⊤ := by sorry
