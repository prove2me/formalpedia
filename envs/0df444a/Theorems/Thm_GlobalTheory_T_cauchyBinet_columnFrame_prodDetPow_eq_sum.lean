-- Prove2me | Theorems.Thm_GlobalTheory_T_cauchyBinet_columnFrame_prodDetPow_eq_sum
-- name    : GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:59.276988+00:00
-- url     : https://prove2.me/theorems/11e76beb-6620-4d73-aa96-ca6119567427
-- title:
--   T: cauchy Binet column Frame prod Det Pow eq sum
-- statement:
--   The T construction uses the cauchy Binet column Frame prod Det Pow eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSumStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CauchyBinetColumnFrameProdDetPowEqSumStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSum
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.cauchyBinet_columnFrame_prodDetPow_eq_sum : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ) (x₀ : GlobalTheory.MinorFrame.Var ι d a → ℂ), GlobalTheory.MinorFrame.rsub (GlobalTheory.MinorFrame.frameMat x₀).conjTranspose (GlobalTheory.MinorFrame.detG a n) = ∑ T : GlobalTheory.MinorFrame.Tup ι a d n, star (MvPolynomial.eval x₀ (GlobalTheory.MinorFrame.prodMinors T)) • GlobalTheory.MinorFrame.prodMinors T := by sorry
