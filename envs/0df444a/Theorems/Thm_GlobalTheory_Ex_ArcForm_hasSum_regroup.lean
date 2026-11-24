-- Prove2me | Theorems.Thm_GlobalTheory_Ex_ArcForm_hasSum_regroup
-- name    : GlobalTheory.Ex.ArcForm.hasSum_regroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:09.138881+00:00
-- url     : https://prove2.me/theorems/1aa1cbd9-18ea-4036-9b3e-8ef0da678a60
-- title:
--   Arc Form: has Sum regroup
-- statement:
--   The Arc Form construction uses the has Sum regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L12-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L12-L28

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

theorem GlobalTheory.Ex.ArcForm.hasSum_regroup {X : Type} (e : X → ℤ) (h0 : ∀ χ, 0 ≤ e χ) (hf : ∀ n : ℤ, {χ | e χ = n}.Finite)
    (a : X → ℂ) (u x : ℂ) (h : HasSum (fun χ => u ^ e χ * a χ) x) :
    HasSum (fun n : ℕ => (∑ᶠ (χ : X) (_ : e χ = n), a χ) * u ^ n) x := by sorry
