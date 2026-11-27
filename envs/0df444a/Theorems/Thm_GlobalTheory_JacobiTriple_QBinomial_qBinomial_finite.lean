-- Prove2me | Theorems.Thm_GlobalTheory_JacobiTriple_QBinomial_qBinomial_finite
-- name    : GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:34:55.705291+00:00
-- url     : https://prove2.me/theorems/34436e0f-9bad-487f-a6bc-76f925e8ddac
-- title:
--   QBinomial: q Binomial finite
-- statement:
--   The QBinomial construction uses the q Binomial finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QBinomialFinite.lean#L46-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/QBinomialFinite.lean#L46-L85

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

theorem GlobalTheory.JacobiTriple.QBinomial.qBinomial_finite : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by sorry
