-- Prove2me | Theorems.Thm_GlobalTheory_PullBdd_bchar_castFrame
-- name    : GlobalTheory.PullBdd.bchar_castFrame
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:02:06.421462+00:00
-- url     : https://prove2.me/theorems/b7e513ea-6fb9-4481-96e6-1238166eb8e4
-- title:
--   Pull Bdd: bchar cast Frame
-- statement:
--   The Pull Bdd construction uses the bchar cast Frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L22-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_TwoLevelLogarithm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLevelBlockOfEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CuspFormPullbackIsBoundedSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open scoped Matrix
open GlobalTheory GlobalTheory.PullBdd
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.PullBdd.bchar_castFrame {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (la : Wt Ψ' r) (b : Frame Ψ r) :
    bchar la (castFrame h b) = bchar (castWt h la) b := by sorry
