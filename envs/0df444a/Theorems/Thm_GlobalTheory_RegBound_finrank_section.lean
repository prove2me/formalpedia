-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_finrank_section
-- name    : GlobalTheory.RegBound.finrank_section
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:31.585514+00:00
-- url     : https://prove2.me/theorems/45a2d87d-527f-47cf-9b09-c0f144d4a83a
-- title:
--   Reg Bound: finrank section
-- statement:
--   The Reg Bound construction uses the finrank section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L95-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L95-L132

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

theorem GlobalTheory.RegBound.finrank_section [Finite σ] {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) (hne : I ≠ ⊤) (e : ℕ) :
    finrank K (piece (I ⊔ Ideal.span {h}) (e + 1)) + finrank K (piece I e) =
      finrank K (piece I (e + 1)) + finrank K (homogeneousSubmodule σ K e) := by sorry
