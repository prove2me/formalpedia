-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_TermUnit_norm_term
-- name    : GlobalTheory.CMVal.TermUnit.norm_term
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:11.060668+00:00
-- url     : https://prove2.me/theorems/9f4f5906-8552-42ea-94d4-d0c52339f33d
-- title:
--   Term Unit: norm term
-- statement:
--   The Term Unit construction uses the norm term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ProdNormSq.lean#L83-L96

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.CMVal.TermUnit.norm_term [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by sorry
