-- Prove2me | Theorems.Thm_GlobalTheory_MxDet_det_comb
-- name    : GlobalTheory.MxDet.det_comb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:30:41.095355+00:00
-- url     : https://prove2.me/theorems/7093dac0-d903-4dd1-b9dd-c620e1e1c692
-- title:
--   Mx Det: det comb
-- statement:
--   The Mx Det construction uses the det comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L41-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L41-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReDetRelation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.MxDet

theorem GlobalTheory.MxDet.det_comb {ι : Type} [Fintype ι] (e : ℕ) (H : ι → Matrix (Fin e) (Fin e) ℂ) (x : ι → ℝ) :
    (∑ i, (x i : ℂ) • H i).det = ∑ c : Fin e → ι, ((∏ l, x (c l) : ℝ) : ℂ) *
      ∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l := by sorry
