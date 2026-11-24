-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_exists_regular_form
-- name    : GlobalTheory.RegBound.exists_regular_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:15.458444+00:00
-- url     : https://prove2.me/theorems/698331e0-1e01-4987-987c-a1df2c733795
-- title:
--   Reg Bound: exists regular form
-- statement:
--   The Reg Bound construction uses the exists regular form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L52-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L52-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]

theorem GlobalTheory.RegBound.exists_regular_form [Finite σ] [Infinite K] {I : Ideal (MvPolynomial σ K)}
    (hsat : ∀ F, (∀ i, X i * F ∈ I) → F ∈ I) :
    ∃ h : MvPolynomial σ K, h.IsHomogeneous 1 ∧ ∀ F, h * F ∈ I → F ∈ I := by sorry
