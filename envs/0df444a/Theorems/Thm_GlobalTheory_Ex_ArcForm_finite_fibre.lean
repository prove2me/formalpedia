-- Prove2me | Theorems.Thm_GlobalTheory_Ex_ArcForm_finite_fibre
-- name    : GlobalTheory.Ex.ArcForm.finite_fibre
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:07:27.967907+00:00
-- url     : https://prove2.me/theorems/62a63574-2c7c-4329-b9c7-ec73c4753422
-- title:
--   Arc Form: finite fibre
-- statement:
--   The Arc Form construction uses the finite fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L30-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_AevalArcTxEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.ArcForm

theorem GlobalTheory.Ex.ArcForm.finite_fibre {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) {m : ℕ} (hm : m ≠ 0)
    (y : N.X) (n : ℤ) : {χ : N.X | β.be (y + m • χ) (y + m • χ) / (2 * m ^ 2) = n}.Finite := by sorry
