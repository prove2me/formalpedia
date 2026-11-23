-- Prove2me | Theorems.Thm_GlobalTheory_RootNormLowerBound_exists_root_norm_lt
-- name    : GlobalTheory.RootNormLowerBound.exists_root_norm_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:36.406869+00:00
-- url     : https://prove2.me/theorems/ade1256a-d365-4fd6-9a7f-ecc6ebfb59cf
-- title:
--   Root Norm Lower Bound: exists root norm lt
-- statement:
--   The Root Norm Lower Bound construction uses the exists root norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowCardLeNormProd.lean#L16-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PowCardLeNormProd.lean#L16-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RootNormLowerBound

theorem GlobalTheory.RootNormLowerBound.exists_root_norm_lt {F : Polynomial ℂ} (hF : Polynomial.Monic F) {ε : ℝ}
    (hε : (0 : ℝ) < ε) (h0 : ‖Polynomial.coeff F (0 : ℕ)‖ < ε ^ Polynomial.natDegree F) :
    ∃ (t : ℂ), Polynomial.IsRoot F t ∧ ‖t‖ < ε := by sorry
