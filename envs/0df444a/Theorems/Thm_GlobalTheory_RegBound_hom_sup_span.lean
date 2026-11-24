-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_hom_sup_span
-- name    : GlobalTheory.RegBound.hom_sup_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:19:50.5865+00:00
-- url     : https://prove2.me/theorems/2136747e-3e43-4da3-82bd-19d19daa18d2
-- title:
--   Reg Bound: hom sup span
-- statement:
--   The Reg Bound construction uses the hom sup span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L84-L93

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

theorem GlobalTheory.RegBound.hom_sup_span {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) :
    ∀ F ∈ I ⊔ Ideal.span {h}, ∀ e, homogeneousComponent e F ∈ I ⊔ Ideal.span {h} := by sorry
