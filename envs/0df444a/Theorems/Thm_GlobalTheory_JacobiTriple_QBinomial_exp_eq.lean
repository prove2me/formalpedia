-- Prove2me | Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_exp_eq
-- name    : GlobalTheory.JacobiTriple.QBinomial.exp_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:52.508602+00:00
-- url     : https://prove2.me/theorems/a3eac557-2967-43a4-860d-e3535cfd585e
-- title:
--   QBinomial: exp eq
-- statement:
--   The QBinomial construction uses the exp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QBinomialFinite.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QBinomialFinite.lean#L39-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QBinomialFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
open GlobalTheory GlobalTheory.JacobiTriple GlobalTheory.JacobiTriple.QBinomial
open GlobalTheory.JacobiTriple

theorem GlobalTheory.JacobiTriple.QBinomial.exp_eq (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by sorry
