-- Prove2me | Theorems.Thm_GlobalTheory_WeilM_isUWeilSplit_split
-- name    : GlobalTheory.WeilM.isUWeilSplit_split
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:43.091858+00:00
-- url     : https://prove2.me/theorems/35debc45-28ba-4a3a-8aca-66e8dcd4d519
-- title:
--   Weil M: is UWeil Split split
-- statement:
--   The Weil M construction uses the is UWeil Split split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsLocallyConstantSplitOm.lean#L151-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilObjectsInhabited
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsLocallyConstantSplitOm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

theorem GlobalTheory.WeilM.isUWeilSplit_split (ψ : AddChar F ℂ) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (hA : IsHerm (swapA F) JA)
    (hB : IsHerm (swapA F) JB) (σ : κ ≃ α × β) (χ : (F × F)ˣ →* Circle) (hc : Continuous χ)
    (hχ : ResEtaPow (⊥ : Subgroup Fˣ) χ (Fintype.card α)) :
    IsUWeilSplit (swapA F) (sbClass F) ψ (1, -1) JA (dbl JB) (splitDarboux hA hB.dbl (dblNum σ)) χ (diagCols β)
      (splitOm (distribHaarChar F) χ (dbl JB) (dblNum σ)) := by sorry
