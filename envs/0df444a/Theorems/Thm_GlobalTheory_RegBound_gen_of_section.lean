-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_gen_of_section
-- name    : GlobalTheory.RegBound.gen_of_section
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:20:40.454961+00:00
-- url     : https://prove2.me/theorems/38ac7e46-28ff-4f13-bba5-6addc08c273e
-- title:
--   Reg Bound: gen of section
-- statement:
--   The Reg Bound construction uses the gen of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L141-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L141-L165

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

theorem GlobalTheory.RegBound.gen_of_section {I : Ideal (MvPolynomial σ K)}
    (hI : ∀ F ∈ I, ∀ e, homogeneousComponent e F ∈ I) {h : MvPolynomial σ K}
    (hh : h.IsHomogeneous 1) (hreg : ∀ F, h * F ∈ I → F ∈ I) {e : ℕ} {F : MvPolynomial σ K}
    (hF : F ∈ I) (hFe : F.IsHomogeneous (e + 1)) (hg : F ∈ genIn (I ⊔ Ideal.span {h}) e) :
    F ∈ genIn I e := by sorry
