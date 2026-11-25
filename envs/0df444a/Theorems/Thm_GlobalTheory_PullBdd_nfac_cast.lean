-- Prove2me | Theorems.Thm_GlobalTheory_PullBdd_nfac_cast
-- name    : GlobalTheory.PullBdd.nfac_cast
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:56:28.872909+00:00
-- url     : https://prove2.me/theorems/a81d1973-618d-4657-92a8-1c82ff4a6a0a
-- title:
--   Pull Bdd: nfac cast
-- statement:
--   The Pull Bdd construction uses the nfac cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CuspFormPullbackIsBoundedSection.lean#L58-L64

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

theorem GlobalTheory.PullBdd.nfac_cast {Ψ Ψ' : Finset (E →+* ℂ)} (h : Ψ = Ψ') (G : Matrix (Fin r) (Fin r) E)
    (la : Wt Ψ' r) (x : Frame Ψ r) :
    (∏ τ : Ψ', ∏ i : Fin r, ‖dmin G (castFrame h x) τ i.succ / dmin G (castFrame h x) τ i.castSucc‖ ^
      (-(la τ i : ℝ) / 2)) =
    ∏ τ : Ψ, ∏ i : Fin r, ‖dmin G x τ i.succ / dmin G x τ i.castSucc‖ ^
      (-(castWt h la τ i : ℝ) / 2) := by sorry
