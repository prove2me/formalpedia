-- Prove2me | Theorems.Thm_GlobalTheory_LineThrough_eval_zero_lineMap
-- name    : GlobalTheory.LineThrough.eval_zero_lineMap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:21.30898+00:00
-- url     : https://prove2.me/theorems/06440eac-7526-409d-8106-d68e047ab335
-- title:
--   Line Through: eval zero line Map
-- statement:
--   The Line Through construction uses the eval zero line Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L31-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough

theorem GlobalTheory.LineThrough.eval_zero_lineMap {d : ℕ} (a c : Fin d → ℂ) (f : MvPolynomial (Fin d) ℂ) :
    (lineMap a c f).eval 0 = MvPolynomial.eval a f := by sorry
