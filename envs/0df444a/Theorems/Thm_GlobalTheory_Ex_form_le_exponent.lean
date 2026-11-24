-- Prove2me | Theorems.Thm_GlobalTheory_Ex_form_le_exponent
-- name    : GlobalTheory.Ex.form_le_exponent
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:06:26.003609+00:00
-- url     : https://prove2.me/theorems/608b0c9e-be0d-4082-a5bd-c13f93c39259
-- title:
--   Ex: form le exponent
-- statement:
--   The Ex construction uses the form le exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArc.lean#L71-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TwistTxEvEqMapArc.lean#L71-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTermsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HasSumMapPowerSeriesMkFinsum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTxEvEqMapArc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.Ex.form_le_exponent {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ^ 2 ∣ k)
    {j : ℕ} (hj : j ∣ k) (hj0 : j ≠ 0) (x z : N.X) (s : ℤ) (hs : (m : ℤ) ^ 2 * β.be z z ≤ s) :
    β.be x x ≤ 4 * (m : ℤ) ^ 2 * (β.be x x / (2 * m ^ 2) + β.be z x / j + s) := by sorry
