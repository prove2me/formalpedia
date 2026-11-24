-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_exists_saturation
-- name    : GlobalTheory.RegBound.exists_saturation
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:15.31781+00:00
-- url     : https://prove2.me/theorems/10ad4973-59b8-4d33-825b-4e121b963337
-- title:
--   Reg Bound: exists saturation
-- statement:
--   The Reg Bound construction uses the exists saturation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L217-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L217-L243

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

theorem GlobalTheory.RegBound.exists_saturation [Finite σ] {J : Ideal (MvPolynomial σ K)}
    (hJ : ∀ F ∈ J, ∀ e, homogeneousComponent e F ∈ J) :
    ∃ J' : Ideal (MvPolynomial σ K), J ≤ J' ∧ (∀ F ∈ J', ∀ e, homogeneousComponent e F ∈ J') ∧
      (∀ F, (∀ i, X i * F ∈ J') → F ∈ J') ∧
      ∀ᶠ e in atTop, ∀ F ∈ J', F.IsHomogeneous e → F ∈ J := by sorry
