-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_siegelRule_split
-- name    : GlobalTheory.WeilM.siegelRule_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:55:37.446067+00:00
-- url     : https://prove2.me/theorems/8adc6a91-5c4f-4f21-9ee5-58bfab712fa5
-- title:
--   Weil M: siegel Rule split
-- statement:
--   The Weil M construction uses the siegel Rule split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L124-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeilObjectsInhabited.lean#L124-L195

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {α β κ : Type}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] [Invertible (2 : F)]

theorem GlobalTheory.WeilM.siegelRule_split (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {JA : Matrix α α (F × F)}
    {JB : Matrix β β (F × F)} (hA : IsHerm (swapA F) JA) (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β)
    (χ : (F × F)ˣ →* Circle) (hχ : ∀ a : Fˣ, χ (Units.map (algebraMap F (F × F) : F →* F × F) a) = 1) :
    SiegelRule (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) := by sorry
