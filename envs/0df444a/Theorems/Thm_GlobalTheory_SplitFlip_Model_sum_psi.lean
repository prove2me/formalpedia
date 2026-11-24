-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_sum_psi
-- name    : GlobalTheory.SplitFlip.Model.sum_psi
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:44.977527+00:00
-- url     : https://prove2.me/theorems/268f10aa-3391-450f-95fd-09741bf86d07
-- title:
--   Model: sum psi
-- statement:
--   The Model construction uses the sum psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L50-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L50-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
open Classical

theorem GlobalTheory.SplitFlip.Model.sum_psi {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ) (s s' : Res k e) :
    ∑ t : Res k e, (ψ (((Quotient.out t : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)))) : ℂ) =
      if s = s' then (Fintype.card (Res k e) : ℂ) else 0 := by sorry
