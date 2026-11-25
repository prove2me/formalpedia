-- Prove2me | Theorems.Thm_GlobalTheory_PullBdd_castFrame_rmul
-- name    : GlobalTheory.PullBdd.castFrame_rmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:01:31.962058+00:00
-- url     : https://prove2.me/theorems/296f455b-a1d1-4787-bee3-af5533339b3f
-- title:
--   Pull Bdd: cast Frame rmul
-- statement:
--   The Pull Bdd construction uses the cast Frame rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L26-L27

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

theorem GlobalTheory.PullBdd.castFrame_rmul {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFrame h (rmul x b) = rmul (castFrame h x) (castFrame h b) := by sorry
