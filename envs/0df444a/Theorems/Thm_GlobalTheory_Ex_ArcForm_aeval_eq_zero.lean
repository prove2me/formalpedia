-- Prove2me | Theorems.Thm_GlobalTheory_Ex_ArcForm_aeval_eq_zero
-- name    : GlobalTheory.Ex.ArcForm.aeval_eq_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:14.107938+00:00
-- url     : https://prove2.me/theorems/b188a46e-7f10-4cd2-a90a-aca668af67f1
-- title:
--   Arc Form: aeval eq zero
-- statement:
--   The Arc Form construction uses the aeval eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L65-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L65-L87

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

theorem GlobalTheory.Ex.ArcForm.aeval_eq_zero {ι : Type} (f : ι → PowerSeries ℂ) (F : MvPolynomial ι ℂ) {ε : ℝ} (hε : 0 < ε)
    (v : ℂˣ → ι → ℂ) (hs : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → ∀ i,
      HasSum (fun n => PowerSeries.coeff n (f i) * (u : ℂ) ^ n) (v u i))
    (hF : ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → MvPolynomial.eval (v u) F = 0) : MvPolynomial.aeval f F = 0 := by sorry
