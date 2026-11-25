-- Prove2me | Theorems.Thm_GlobalTheory_Ex_ArcForm_aeval_arcTx_eq_zero
-- name    : GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:33.629803+00:00
-- url     : https://prove2.me/theorems/f4175f84-ee12-4f56-aabf-29d4dc94b6cb
-- title:
--   Arc Form: aeval arc Tx eq zero
-- statement:
--   The Arc Form construction uses the aeval arc Tx eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/AevalArcTxEqZero.lean#L89-L92

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

theorem GlobalTheory.Ex.ArcForm.aeval_arcTx_eq_zero : ∀ (N : NumD ℂ) (k : ℕ) (β : N.Form k) (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∀ (ι : Type) (p : ι → N.QT (m ^ 2)) (F : MvPolynomial ι ℂ) (ε : ℝ), 0 < ε → (∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ i, Summable fun χ => ‖(N.twist β u).txT m (N.twQ β u hm (p i)) χ‖) ∧ MvPolynomial.eval (fun i => (N.twist β u).tx m (N.twQ β u hm (p i))) F = 0) → MvPolynomial.aeval (fun i => N.arcTx β.be m (p i)) F = 0 := by sorry
