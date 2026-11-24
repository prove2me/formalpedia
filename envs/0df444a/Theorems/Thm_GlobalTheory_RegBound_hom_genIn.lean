-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_hom_genIn
-- name    : GlobalTheory.RegBound.hom_genIn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:10.947095+00:00
-- url     : https://prove2.me/theorems/e431565f-082e-4d11-b5fc-d56dc81eeba0
-- title:
--   Reg Bound: hom gen In
-- statement:
--   The Reg Bound construction uses the hom gen In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L134-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L134-L139

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

theorem GlobalTheory.RegBound.hom_genIn (I : Ideal (MvPolynomial σ K)) (d : ℕ) :
    ∀ F ∈ genIn I d, ∀ e, homogeneousComponent e F ∈ genIn I d := by sorry
