-- Prove2me | Theorems.Thm_GlobalTheory_RegBound_gen_top
-- name    : GlobalTheory.RegBound.gen_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:02.991612+00:00
-- url     : https://prove2.me/theorems/6964eb79-a1b6-4f3e-9663-ee977e321d29
-- title:
--   Reg Bound: gen top
-- statement:
--   The Reg Bound construction uses the gen top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L167-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean#L167-L174

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

theorem GlobalTheory.RegBound.gen_top {e : ℕ} {F : MvPolynomial σ K} (hFe : F.IsHomogeneous (e + 1)) :
    F ∈ genIn (⊤ : Ideal (MvPolynomial σ K)) e := by sorry
