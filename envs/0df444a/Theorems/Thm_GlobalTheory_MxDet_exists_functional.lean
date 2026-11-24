-- Prove2me | Theorems.Thm_GlobalTheory_MxDet_exists_functional
-- name    : GlobalTheory.MxDet.exists_functional
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:30:19.556899+00:00
-- url     : https://prove2.me/theorems/191881de-e127-43c3-8446-ed09b2a4ee83
-- title:
--   Mx Det: exists functional
-- statement:
--   The Mx Det construction uses the exists functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L31-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ReDetRelation.lean#L31-L39

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

theorem GlobalTheory.MxDet.exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (linF x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by sorry
